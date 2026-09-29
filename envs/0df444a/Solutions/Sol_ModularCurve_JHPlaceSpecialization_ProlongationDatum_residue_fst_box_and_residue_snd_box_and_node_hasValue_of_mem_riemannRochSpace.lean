-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c6c37da5-97e3-5c43-9603-b2d924dddb67

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_pos_sp_sub_algebraMap_of_ord_pos
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_not_isInftySide_of_isZeroSide
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃"
p2m_attr_erase "simp" "ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero"
p2m_attr_erase "simp" "Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar"

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace.AlgebraicCurve IsLocalRing ModularCurve"
open scoped MatrixGroups

noncomputable section

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.ord_restrictAlong Place Place.ord Place.ord_zero Place.ord_one Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor SemilinearAut SemilinearAut.ofAlgAut RegularProlongation ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul riemannRochSpace mem_riemannRochSpace_iff finiteDimensional_lSpace finiteDimensional_lSpace_zero nonempty_place_of_transcendental_of_finiteDimensional"
namespace OrderBox
p2m_open "AlgebraicCurve"

section Core

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private structure IsOrderFun (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    (v : V → ℤ) : Prop where
  min_le_add : ∀ x y : V, x ≠ 0 → y ≠ 0 → x + y ≠ 0 → min (v x) (v y) ≤ v (x + y)
  smul_eq : ∀ (c : K) (x : V), c ≠ 0 → x ≠ 0 → v (c • x) = v x

namespace IsOrderFun

variable {v : V → ℤ}

private theorem zero_or_le_add (hv : IsOrderFun K v) {n : ℤ} {x y : V}
    (hx : x = 0 ∨ n ≤ v x) (hy : y = 0 ∨ n ≤ v y) : x + y = 0 ∨ n ≤ v (x + y) := by
  by_cases hx0 : x = 0
  · subst hx0
    rwa [zero_add]
  by_cases hy0 : y = 0
  · subst hy0
    rwa [add_zero]
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  have h := hv.min_le_add x y hx0 hy0 hxy
  have hx' := hx.resolve_left hx0
  have hy' := hy.resolve_left hy0
  right
  omega

private theorem zero_or_le_smul (hv : IsOrderFun K v) {n : ℤ} (c : K) {x : V}
    (hx : x = 0 ∨ n ≤ v x) : c • x = 0 ∨ n ≤ v (c • x) := by
  by_cases hc : c = 0
  · left
    rw [hc, zero_smul]
  by_cases hx0 : x = 0
  · left
    rw [hx0, smul_zero]
  right
  rw [hv.smul_eq c x hc hx0]
  exact hx.resolve_left hx0

private theorem zero_or_le_sum (hv : IsOrderFun K v) {n : ℤ} {ι : Type*} (s : Finset ι) (f : ι → V)
    (h : ∀ i ∈ s, f i = 0 ∨ n ≤ v (f i)) : (∑ i ∈ s, f i) = 0 ∨ n ≤ v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Or.inl Finset.sum_empty
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hv.zero_or_le_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private def box (hv : IsOrderFun K v) (n : ℤ) : Submodule K V where
  carrier := {x | x = 0 ∨ n ≤ v x}
  zero_mem' := Or.inl rfl
  add_mem' hx hy := hv.zero_or_le_add hx hy
  smul_mem' c _ hx := hv.zero_or_le_smul c hx

private theorem mem_box (hv : IsOrderFun K v) {n : ℤ} {x : V} : x ∈ hv.box n ↔ x = 0 ∨ n ≤ v x :=
  Iff.rfl

private theorem linearIndependent_of_injective (hv : IsOrderFun K v) {ι : Type*} (f : ι → V)
    (hf : ∀ i, f i ≠ 0) (hinj : Function.Injective fun i => v (f i)) :
    LinearIndependent K f := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci

  obtain ⟨i₀, hi₀, hmin⟩ := (s.filter fun j => c j ≠ 0).exists_min_image (fun j => v (f j))
    ⟨i, Finset.mem_filter.mpr ⟨hi, hci⟩⟩
  obtain ⟨hi₀s, hci₀⟩ := Finset.mem_filter.mp hi₀

  have hrest : ∀ j ∈ s.erase i₀, c j • f j = 0 ∨ v (f i₀) + 1 ≤ v (c j • f j) := by
    intro j hj
    by_cases hcj : c j = 0
    · left
      rw [hcj, zero_smul]
    right
    rw [hv.smul_eq _ _ hcj (hf j)]
    have hle := hmin j (Finset.mem_filter.mpr ⟨Finset.mem_of_mem_erase hj, hcj⟩)
    have hne : v (f j) ≠ v (f i₀) := fun h => Finset.ne_of_mem_erase hj (hinj h)
    omega
  have hbox := hv.zero_or_le_sum (s.erase i₀) (fun j => c j • f j) hrest

  have hlead : c i₀ • f i₀ = -∑ j ∈ s.erase i₀, c j • f j := by
    rw [← Finset.add_sum_erase s _ hi₀s] at hsum
    exact eq_neg_of_add_eq_zero_left hsum
  have hne0 : c i₀ • f i₀ ≠ 0 := smul_ne_zero hci₀ (hf i₀)
  rcases hbox with h0 | hle
  · exact hne0 (by rw [hlead, h0, neg_zero])
  · have hneg : v (c i₀ • f i₀) = v (∑ j ∈ s.erase i₀, c j • f j) := by
      rw [hlead, ← neg_one_smul K, hv.smul_eq _ _ (by norm_num) (fun h => hne0 (by
        rw [hlead, h, neg_zero]))]
    rw [← hneg, hv.smul_eq _ _ hci₀ (hf i₀)] at hle
    omega

private theorem finite_image (hv : IsOrderFun K v) (M : Submodule K V) [FiniteDimensional K M] :
    (v '' {x | x ∈ M ∧ x ≠ 0}).Finite := by
  classical
  by_contra hinf
  obtain ⟨T, hTsub, hTcard⟩ := Set.not_finite.mp hinf |>.exists_subset_card_eq
    (Module.finrank K M + 1)
  have hw : ∀ n ∈ T, ∃ x : V, (x ∈ M ∧ x ≠ 0) ∧ v x = n := fun n hn =>
    hTsub (Finset.mem_coe.mpr hn)
  choose! g hg using hw
  have hli : LinearIndependent K (fun n : T => (⟨g n, (hg n n.2).1.1⟩ : M)) := by
    refine LinearIndependent.of_comp M.subtype ?_
    refine hv.linearIndependent_of_injective (fun n : T => g n) (fun n => (hg n n.2).1.2) ?_
    intro a b hab
    apply Subtype.ext
    have ha := (hg a a.2).2
    have hb := (hg b b.2).2
    simp only at hab
    rw [ha, hb] at hab
    exact hab
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, hTcard] at hcard
  omega

end IsOrderFun

variable {V₁ : Type*} [AddCommGroup V₁] [Module K V₁] {V₂ : Type*} [AddCommGroup V₂] [Module K V₂]

private theorem exists_box [Infinite K] {v₁ : V₁ → ℤ} {v₂ : V₂ → ℤ}
    (hv₁ : IsOrderFun K v₁) (hv₂ : IsOrderFun K v₂)
    (M : Submodule K (V₁ × V₂)) [FiniteDimensional K M] (m : ℤ)
    (e : V₁ × V₂) (he : e ∈ M) (he₁ : e.1 ≠ 0) (he₂ : e.2 ≠ 0)
    (hve₁ : v₁ e.1 = 0) (hve₂ : v₂ e.2 = 0)
    (hlaw : ∀ g ∈ M, g.1 ≠ 0 → g.2 ≠ 0 → -m ≤ v₁ g.1 + v₂ g.2) :
    ∃ s : ℤ, -m ≤ s ∧ s ≤ 0 ∧
      ∀ g ∈ M, (g.1 = 0 ∨ s ≤ v₁ g.1) ∧ (g.2 = 0 ∨ -m - s ≤ v₂ g.2) := by
  classical
  have hm : 0 ≤ m := by
    have h := hlaw e he he₁ he₂
    rw [hve₁, hve₂] at h
    omega

  set T : Set ℤ := v₁ '' {x | x ∈ M.map (LinearMap.fst K V₁ V₂) ∧ x ≠ 0} with hT
  haveI : Finite T := (hv₁.finite_image (M.map (LinearMap.fst K V₁ V₂))).to_subtype
  have h0T : (0 : ℤ) ∈ T := ⟨e.1, ⟨⟨e, he, rfl⟩, he₁⟩, hve₁⟩

  let B : T → Submodule K (V₁ × V₂) := fun t => (hv₁.box (t : ℤ)).prod (hv₂.box (-m - (t : ℤ)))
  have hmemB : ∀ (t : T) (g : V₁ × V₂),
      g ∈ B t ↔ (g.1 = 0 ∨ (t : ℤ) ≤ v₁ g.1) ∧ (g.2 = 0 ∨ -m - (t : ℤ) ≤ v₂ g.2) := fun t g => by
    simp only [B, Submodule.mem_prod, IsOrderFun.mem_box]

  have hsnd : ∀ g ∈ M, g.1 = 0 → g.2 ≠ 0 → -m ≤ v₂ g.2 := by
    intro g hg hg1 hg2

    obtain ⟨c, hc0, hc⟩ : ∃ c : K, c ≠ 0 ∧ g.2 + c • e.2 ≠ 0 := by
      by_cases h1 : g.2 + (1 : K) • e.2 ≠ 0
      · exact ⟨1, one_ne_zero, h1⟩
      obtain ⟨d, hd⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset K)
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hd
      refine ⟨d, hd.1, fun hd' => hd.2 ?_⟩
      push Not at h1
      have hsub : (d - 1) • e.2 = 0 := by
        rw [sub_smul, sub_eq_zero]
        exact (neg_eq_of_add_eq_zero_right hd').symm.trans (neg_eq_of_add_eq_zero_right h1)
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right he₂)
    have hgc : g + c • e ∈ M := M.add_mem hg (M.smul_mem c he)
    have hfst : (g + c • e).1 = c • e.1 := by rw [Prod.fst_add, Prod.smul_fst, hg1, zero_add]
    have hsnd' : (g + c • e).2 = g.2 + c • e.2 := by rw [Prod.snd_add, Prod.smul_snd]
    have hl := hlaw (g + c • e) hgc (by rw [hfst]; exact smul_ne_zero hc0 he₁)
      (by rw [hsnd']; exact hc)
    rw [hfst, hv₁.smul_eq c e.1 hc0 he₁, hve₁, zero_add, hsnd'] at hl

    have hb₁ : g.2 + c • e.2 = 0 ∨ -m ≤ v₂ (g.2 + c • e.2) := Or.inr hl
    have hb₂ : (-c) • e.2 = 0 ∨ -m ≤ v₂ ((-c) • e.2) := by
      right
      rw [hv₂.smul_eq _ _ (neg_ne_zero.mpr hc0) he₂, hve₂]
      omega
    have h := hv₂.zero_or_le_add hb₁ hb₂
    rw [neg_smul, add_neg_cancel_right] at h
    exact h.resolve_left hg2

  have hcover : ∀ g ∈ M, ∃ t : T, g ∈ B t := by
    intro g hg
    by_cases hg1 : g.1 = 0
    · refine ⟨⟨0, h0T⟩, (hmemB _ _).mpr ⟨Or.inl hg1, ?_⟩⟩
      by_cases hg2 : g.2 = 0
      · exact Or.inl hg2
      · right
        have h := hsnd g hg hg1 hg2
        show -m - 0 ≤ v₂ g.2
        omega
    · refine ⟨⟨v₁ g.1, g.1, ⟨⟨g, hg, rfl⟩, hg1⟩, rfl⟩, (hmemB _ _).mpr ⟨Or.inr le_rfl, ?_⟩⟩
      by_cases hg2 : g.2 = 0
      · exact Or.inl hg2
      · right
        have h := hlaw g hg hg1 hg2
        show -m - v₁ g.1 ≤ v₂ g.2
        omega

  obtain ⟨t, ht⟩ : ∃ t : T, (B t).comap M.subtype = ⊤ := by
    by_contra hnone
    push Not at hnone
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hnone
    obtain ⟨t, hxt⟩ := hcover (x : V₁ × V₂) x.2
    exact hx t hxt
  have hall : ∀ g ∈ M, g ∈ B t := fun g hg => by
    have h : (⟨g, hg⟩ : M) ∈ (B t).comap M.subtype := by
      rw [ht]
      exact Submodule.mem_top
    exact h
  have heB := (hmemB t e).mp (hall e he)
  refine ⟨t, ?_, ?_, fun g hg => (hmemB t g).mp (hall g hg)⟩
  · rcases heB.2 with h | h
    · exact absurd h he₂
    · rw [hve₂] at h
      omega
  · rcases heB.1 with h | h
    · exact absurd h he₁
    · rwa [hve₁] at h

end Core

section PlaceOrder

open IsLocalRing

variable {k₀ k F : Type*} [Field k₀] [Field k] [Field F] [Algebra k F]
  [Algebra k₀ k] [Algebra k₀ F] [IsScalarTower k₀ k F]

private theorem min_placeOrd_le_placeOrd_add (w : Place k F) {x y : F} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (w.ord x) (w.ord y) ≤ w.ord (x + y) := by
  have hux := w.adicValuation_ne_zero hx
  have huy := w.adicValuation_ne_zero hy
  have huxy := w.adicValuation_ne_zero hxy
  unfold Place.ord
  rcases le_max_iff.mp (w.adicValuation.map_add x y) with h | h
  · have h' := (WithZero.log_le_log huxy hux).mpr h
    exact (min_le_left _ _).trans (by omega)
  · have h' := (WithZero.log_le_log huxy huy).mpr h
    exact (min_le_right _ _).trans (by omega)

private theorem isOrderFun_placeOrd (w : Place k F) : IsOrderFun k₀ (V := F) (fun x => w.ord x) where
  min_le_add x y hx hy hxy := min_placeOrd_le_placeOrd_add w hx hy hxy
  smul_eq c x hc hx := by
    show w.ord (c • x) = w.ord x
    rw [← IsScalarTower.algebraMap_smul k c x]
    exact ConstantReduction.ord_smul w ((map_ne_zero (algebraMap k₀ k)).mpr hc) x

end PlaceOrder

section Pair

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
  {k Fk : Type*} [Field k] [Field Fk] [Algebra k Fk]
  [Algebra (ResidueField A) k] [Algebra (ResidueField A) Fk] [IsScalarTower (ResidueField A) k Fk]

private def pairSpace (R₁ R₂ : RegularProlongation A F Fb) (ι : Fb →+* Fk)
    (hι : ∀ c, ι (algebraMap (ResidueField A) Fb c) = algebraMap (ResidueField A) Fk c)
    (W : Submodule L F) : Submodule (ResidueField A) (Fk × Fk) where
  carrier := {g | ∃ (f : F) (_ : f ∈ W) (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
    g = (ι (R₁.residue ⟨f, h₁⟩), ι (R₂.residue ⟨f, h₂⟩))}
  zero_mem' := by
    refine ⟨0, W.zero_mem, R₁.integers.zero_mem, R₂.integers.zero_mem, ?_⟩
    have e₁ : (⟨(0 : F), R₁.integers.zero_mem⟩ : R₁.integers) = 0 := rfl
    have e₂ : (⟨(0 : F), R₂.integers.zero_mem⟩ : R₂.integers) = 0 := rfl
    rw [e₁, e₂]
    simp only [map_zero]
    rfl
  add_mem' := by
    rintro g g' ⟨f, hf, h₁, h₂, rfl⟩ ⟨f', hf', h₁', h₂', rfl⟩
    refine ⟨f + f', W.add_mem hf hf', add_mem h₁ h₁', add_mem h₂ h₂', ?_⟩
    have e₁ : (⟨f + f', add_mem h₁ h₁'⟩ : R₁.integers) = ⟨f, h₁⟩ + ⟨f', h₁'⟩ := rfl
    have e₂ : (⟨f + f', add_mem h₂ h₂'⟩ : R₂.integers) = ⟨f, h₂⟩ + ⟨f', h₂'⟩ := rfl
    rw [e₁, e₂]
    simp only [map_add]
    rfl
  smul_mem' := by
    rintro c g ⟨f, hf, h₁, h₂, rfl⟩
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    have ha₁ : algebraMap L F (a : L) ∈ R₁.integers := (R₁.algebraMap_mem_iff _).mpr a.2
    have ha₂ : algebraMap L F (a : L) ∈ R₂.integers := (R₂.algebraMap_mem_iff _).mpr a.2
    refine ⟨algebraMap L F (a : L) * f, ?_, mul_mem ha₁ h₁, mul_mem ha₂ h₂, ?_⟩
    · rw [← Algebra.smul_def]
      exact W.smul_mem _ hf
    have e₁ : (⟨algebraMap L F (a : L) * f, mul_mem ha₁ h₁⟩ : R₁.integers)
        = ⟨_, ha₁⟩ * ⟨f, h₁⟩ := rfl
    have e₂ : (⟨algebraMap L F (a : L) * f, mul_mem ha₂ h₂⟩ : R₂.integers)
        = ⟨_, ha₂⟩ * ⟨f, h₂⟩ := rfl
    rw [e₁, e₂]
    simp only [map_mul, R₁.residue_algebraMap a, R₂.residue_algebraMap a, hι]
    rw [Prod.smul_mk, Algebra.smul_def, Algebra.smul_def]

private theorem exists_box_of_orderLaw [Infinite (ResidueField A)]
    (R₁ R₂ : RegularProlongation A F Fb) (ι : Fb →+* Fk)
    (hι : ∀ c, ι (algebraMap (ResidueField A) Fb c) = algebraMap (ResidueField A) Fk c)
    (W : Submodule L F) (h1 : (1 : F) ∈ W)
    [FiniteDimensional (ResidueField A) (pairSpace R₁ R₂ ι hι W)]
    (w₁ w₂ : Place k Fk) (m : ℤ)
    (hlaw : ∀ (f : F), f ∈ W → ∀ (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
      R₁.residue ⟨f, h₁⟩ ≠ 0 → R₂.residue ⟨f, h₂⟩ ≠ 0 →
        -m ≤ w₁.ord (ι (R₁.residue ⟨f, h₁⟩)) + w₂.ord (ι (R₂.residue ⟨f, h₂⟩))) :
    ∃ s : ℤ, -m ≤ s ∧ s ≤ 0 ∧
      ∀ (f : F), f ∈ W → ∀ (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers),
        (ι (R₁.residue ⟨f, h₁⟩) = 0 ∨ s ≤ w₁.ord (ι (R₁.residue ⟨f, h₁⟩))) ∧
        (ι (R₂.residue ⟨f, h₂⟩) = 0 ∨ -m - s ≤ w₂.ord (ι (R₂.residue ⟨f, h₂⟩))) := by
  have hv₁ := isOrderFun_placeOrd (k₀ := ResidueField A) w₁
  have hv₂ := isOrderFun_placeOrd (k₀ := ResidueField A) w₂
  have he : ((1 : Fk), (1 : Fk)) ∈ pairSpace R₁ R₂ ι hι W := by
    refine ⟨1, h1, R₁.integers.one_mem, R₂.integers.one_mem, ?_⟩
    have e₁ : (⟨(1 : F), R₁.integers.one_mem⟩ : R₁.integers) = 1 := rfl
    have e₂ : (⟨(1 : F), R₂.integers.one_mem⟩ : R₂.integers) = 1 := rfl
    rw [e₁, e₂]
    simp only [map_one]
  obtain ⟨s, hs₁, hs₂, hall⟩ := exists_box hv₁ hv₂ (pairSpace R₁ R₂ ι hι W) m ((1 : Fk), (1 : Fk))
    he one_ne_zero one_ne_zero w₁.ord_one w₂.ord_one (by
      rintro g ⟨f, hf, h₁, h₂, rfl⟩ hg₁ hg₂
      exact hlaw f hf h₁ h₂ (fun h => hg₁ (by simp only [h, map_zero]))
        (fun h => hg₂ (by simp only [h, map_zero])))
  exact ⟨s, hs₁, hs₂, fun f hf h₁ h₂ => hall _ ⟨f, hf, h₁, h₂, rfl⟩⟩

end Pair

section Device

open IsLocalRing

variable {L : Type*} [Field L] {A : ValuationSubring L}
  {F : Type*} [Field F] [Algebra L F]
  {Fb : Type*} [Field Fb] [Algebra (ResidueField A) Fb]
  {k Fk : Type*} [Field k] [Field Fk] [Algebra k Fk]
  [Algebra (ResidueField A) k] [Algebra (ResidueField A) Fk] [IsScalarTower (ResidueField A) k Fk]

private theorem exists_forall_mul_inv_mem {ι : Type*} (s : Finset ι) (c : ι → L) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hc₀ : c i₀ ≠ 0) : ∃ j ∈ s, c j ≠ 0 ∧ ∀ i ∈ s, c i * (c j)⁻¹ ∈ A := by
  classical
  obtain ⟨j, hjs, hmax⟩ := s.exists_max_image (fun i => A.valuation (c i)) ⟨i₀, hi₀⟩
  have hvj : A.valuation (c j) ≠ 0 := by
    intro h0
    have h := hmax i₀ hi₀
    rw [h0, le_zero_iff, Valuation.zero_iff] at h
    exact hc₀ h
  refine ⟨j, hjs, fun h => hvj (by rw [h, Valuation.map_zero]), fun i hi => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv]
  calc A.valuation (c i) * (A.valuation (c j))⁻¹
      ≤ A.valuation (c j) * (A.valuation (c j))⁻¹ := by
        gcongr
        exact hmax i hi
    _ = 1 := mul_inv_cancel₀ hvj

private theorem linearIndependent_of_pairs (R₁ R₂ : RegularProlongation A F Fb) (ι : Fb →+* Fk)
    (hι : ∀ c, ι (algebraMap (ResidueField A) Fb c) = algebraMap (ResidueField A) Fk c)
    {I : Type*} (f : I → F) (h₁ : ∀ i, f i ∈ R₁.integers) (h₂ : ∀ i, f i ∈ R₂.integers)
    (hli : LinearIndependent (ResidueField A)
      (fun i => (ι (R₁.residue ⟨f i, h₁ i⟩), ι (R₂.residue ⟨f i, h₂ i⟩)))) :
    LinearIndependent L f := by
  classical
  rw [linearIndependent_iff']
  intro s c hsum i hi
  by_contra hci
  obtain ⟨j, hjs, hcj, hA⟩ := exists_forall_mul_inv_mem (A := A) s c hi hci

  let a : I → A := fun i => if hi : i ∈ s then ⟨c i * (c j)⁻¹, hA i hi⟩ else 0
  have ha : ∀ i ∈ s, ((a i : A) : L) = c i * (c j)⁻¹ := fun i hi => by simp [a, hi]
  have haj : a j = 1 := Subtype.ext (by rw [ha j hjs]; exact mul_inv_cancel₀ hcj)
  have hrel : ∑ i ∈ s, algebraMap L F ((a i : A) : L) * f i = 0 := by
    have h : ∑ i ∈ s, algebraMap L F ((a i : A) : L) * f i = (c j)⁻¹ • ∑ i ∈ s, c i • f i := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ha i hi, ← Algebra.smul_def, smul_smul, mul_comm]
    rw [h, hsum, smul_zero]

  have key : ∀ (R : RegularProlongation A F Fb) (hR : ∀ i, f i ∈ R.integers),
      ∑ i ∈ s, (IsLocalRing.residue A (a i)) • ι (R.residue ⟨f i, hR i⟩) = 0 := by
    intro R hR
    let x : I → R.integers := fun i =>
      ⟨algebraMap L F ((a i : A) : L) * f i, mul_mem ((R.algebraMap_mem_iff _).mpr (a i).2) (hR i)⟩
    have hx0 : ∑ i ∈ s, x i = 0 := Subtype.ext ((map_sum R.integers.subtype x s).trans hrel)
    have h := congrArg (fun y => ι (R.residue y)) hx0
    simp only [map_sum, map_zero] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hxi : x i = ⟨_, (R.algebraMap_mem_iff _).mpr (a i).2⟩ * ⟨f i, hR i⟩ := rfl
    rw [hxi, map_mul, map_mul, R.residue_algebraMap (a i), hι, Algebra.smul_def]
  have hpair : ∑ i ∈ s, (IsLocalRing.residue A (a i)) •
      (ι (R₁.residue ⟨f i, h₁ i⟩), ι (R₂.residue ⟨f i, h₂ i⟩)) = 0 := by
    rw [Prod.ext_iff, Prod.fst_sum, Prod.snd_sum, Prod.fst_zero, Prod.snd_zero]
    exact ⟨(Finset.sum_congr rfl fun i _ => rfl).trans (key R₁ h₁),
      (Finset.sum_congr rfl fun i _ => rfl).trans (key R₂ h₂)⟩
  have h0 := (linearIndependent_iff'.mp hli) s (fun i => IsLocalRing.residue A (a i)) hpair j hjs
  simp only [haj, map_one] at h0
  exact one_ne_zero h0

private theorem finiteDimensional_pairSpace (R₁ R₂ : RegularProlongation A F Fb) (ι : Fb →+* Fk)
    (hι : ∀ c, ι (algebraMap (ResidueField A) Fb c) = algebraMap (ResidueField A) Fk c)
    (W : Submodule L F) [FiniteDimensional L W] :
    FiniteDimensional (ResidueField A) (pairSpace R₁ R₂ ι hι W) := by
  classical
  obtain ⟨T, hTS, hspan, hli⟩ :=
    exists_linearIndependent (ResidueField A) (pairSpace R₁ R₂ ι hι W : Set (Fk × Fk))
  have hTfin : T.Finite := by
    by_contra hinf
    obtain ⟨T', hT', hcard⟩ := Set.not_finite.mp hinf |>.exists_subset_card_eq (Module.finrank L W + 1)
    have hpre : ∀ p ∈ T', ∃ (f : F) (_ : f ∈ W) (hf₁ : f ∈ R₁.integers) (hf₂ : f ∈ R₂.integers),
        p = (ι (R₁.residue ⟨f, hf₁⟩), ι (R₂.residue ⟨f, hf₂⟩)) := fun p hp =>
      hTS (hT' (Finset.mem_coe.mpr hp))
    choose! g hgW hg₁ hg₂ hgp using hpre
    have hsub : LinearIndependent (ResidueField A) (fun p : T' => (p : Fk × Fk)) :=
      hli.comp (fun p : T' => (⟨(p : Fk × Fk), hT' (Finset.mem_coe.mpr p.2)⟩ : T))
        (fun p p' h => Subtype.ext (by simpa using congrArg (fun z : T => (z : Fk × Fk)) h))
    have hliT' : LinearIndependent (ResidueField A)
        (fun p : T' => (ι (R₁.residue ⟨g p, hg₁ p p.2⟩), ι (R₂.residue ⟨g p, hg₂ p p.2⟩))) := by
      have hfeq : (fun p : T' => (ι (R₁.residue ⟨g p, hg₁ p p.2⟩), ι (R₂.residue ⟨g p, hg₂ p p.2⟩)))
          = (fun p : T' => (p : Fk × Fk)) := funext fun p => (hgp p p.2).symm
      rw [hfeq]
      exact hsub
    have hliL : LinearIndependent L (fun p : T' => g p) :=
      linearIndependent_of_pairs R₁ R₂ ι hι _ (fun p => hg₁ p p.2) (fun p => hg₂ p p.2) hliT'
    have hliW : LinearIndependent L (fun p : T' => (⟨g p, hgW p p.2⟩ : W)) :=
      LinearIndependent.of_comp W.subtype hliL
    have hle := hliW.fintype_card_le_finrank
    rw [Fintype.card_coe, hcard] at hle
    omega
  have hspan' : Submodule.span (ResidueField A) T = pairSpace R₁ R₂ ι hι W := by
    rw [hspan, Submodule.span_eq]
  rw [← hspan']
  exact FiniteDimensional.span_of_finite _ hTfin

end Device

end AlgebraicCurve.OrderBox

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace.AlgebraicCurve ModularCurve"

namespace C3H

private theorem neg_mapDomain_filter_le {X Y : Type*} (r : X → Y) (D E : X →₀ ℤ) (p : X → Prop)
    {d₁ d₂ : DecidablePred p} (hDE : ∀ W, -E W ≤ D W) (y : Y) :
    -(Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d₂ E) y)
      ≤ Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d₁ D) y := by
  have hd : d₂ = d₁ := Subsingleton.elim _ _
  subst hd
  have hle : -(Finsupp.filter p E) ≤ Finsupp.filter p D := Finsupp.le_def.mpr fun W => by
    rw [Finsupp.coe_neg, Pi.neg_apply, Finsupp.filter_apply, Finsupp.filter_apply]
    split_ifs
    · exact hDE W
    · rw [neg_zero]
  have hm := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := r) hle) y
  have hneg : Finsupp.mapDomain r (-(Finsupp.filter p E)) = -Finsupp.mapDomain r (Finsupp.filter p E) :=
    map_neg (Finsupp.mapDomain.addMonoidHom r) _
  rw [hneg, Finsupp.coe_neg, Pi.neg_apply] at hm
  exact hm

private theorem mapDomain_filter_nonneg {X Y : Type*} (r : X → Y) (E : X →₀ ℤ) (p : X → Prop)
    {d : DecidablePred p} (hE : ∀ W, 0 ≤ E W) (y : Y) :
    0 ≤ Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d E) y := by
  have hle : (0 : X →₀ ℤ) ≤ Finsupp.filter p E := Finsupp.le_def.mpr fun W => by
    rw [Finsupp.coe_zero, Pi.zero_apply, Finsupp.filter_apply]
    split_ifs
    · exact hE W
    · exact le_rfl
  have hm := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := r) hle) y
  rw [Finsupp.mapDomain_zero, Finsupp.coe_zero, Pi.zero_apply] at hm
  exact hm

private theorem ord_sub_algebraMap_of_ord_lt_zero {K₀ F₀ : Type*} [Field K₀] [Field F₀]
    [Algebra K₀ F₀] (W : Place K₀ F₀) (g : F₀) (c : K₀) (hg : W.ord g < 0) :
    W.ord (g - algebraMap K₀ F₀ c) = W.ord g := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hg
    exact lt_irrefl _ hg
  have hgc0 : g - algebraMap K₀ F₀ c ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    rw [h] at hg
    rcases eq_or_ne c 0 with rfl | hc
    · rw [map_zero, Place.ord_zero] at hg
      exact lt_irrefl _ hg
    · rw [ConstantReduction.ord_algebraMap W hc] at hg
      exact lt_irrefl _ hg
  have hv : W.adicValuation (-(algebraMap K₀ F₀ c)) < W.adicValuation g := by
    rw [Valuation.map_neg, W.adicValuation_eq_exp_neg_ord hg0]
    refine lt_of_le_of_lt (W.adicValuation_algebraMap_le_one c) ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h1 := Valuation.map_add_eq_of_lt_left _ hv
  rw [← sub_eq_add_neg, W.adicValuation_eq_exp_neg_ord hgc0, W.adicValuation_eq_exp_neg_ord hg0] at h1
  have h2 := WithZero.exp_injective h1
  omega

private theorem algebraMap_mem_riemannRochSpace {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    {E : Divisor K₀ F₀} (hE : ∀ W, 0 ≤ E W) (c : K₀) : algebraMap K₀ F₀ c ∈ riemannRochSpace E := by
  rw [mem_riemannRochSpace_iff]
  intro W
  rcases eq_or_ne c 0 with rfl | hc
  · exact Or.inl (map_zero _)
  · refine Or.inr ?_
    rw [ConstantReduction.ord_algebraMap W hc]
    have h := hE W
    omega

private theorem regProl_residue_sub_algebraMap {L : Type*} [Field L] {A : ValuationSubring L}
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R : RegularProlongation A F Fbar) {f : F} (hf : f ∈ R.integers) (a : A) :
    ∃ h : f - algebraMap L F a ∈ R.integers,
      R.residue ⟨f - algebraMap L F a, h⟩
        = R.residue ⟨f, hf⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
  have ha : algebraMap L F a ∈ R.integers := (R.algebraMap_mem_iff a).mpr a.2
  refine ⟨sub_mem hf ha, ?_⟩
  rw [← R.residue_algebraMap a, ← map_sub]
  rfl

private theorem regProl_exists_residue_sub_algebraMap_ne_zero {L : Type*} [Field L]
    {A : ValuationSubring L} [Infinite (ResidueField A)]
    {F : Type*} [Field F] [Algebra L F] {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
    (R₁ R₂ : RegularProlongation A F Fbar) {f : F} (h₁ : f ∈ R₁.integers) (h₂ : f ∈ R₂.integers) :
    ∃ (a : A) (g₁ : f - algebraMap L F a ∈ R₁.integers) (g₂ : f - algebraMap L F a ∈ R₂.integers),
      R₁.residue ⟨f - algebraMap L F a, g₁⟩ ≠ 0 ∧ R₂.residue ⟨f - algebraMap L F a, g₂⟩ ≠ 0 ∧
      R₁.residue ⟨f - algebraMap L F a, g₁⟩
        = R₁.residue ⟨f, h₁⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) ∧
      R₂.residue ⟨f - algebraMap L F a, g₂⟩
        = R₂.residue ⟨f, h₂⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A a) := by
  classical
  have hinj : Function.Injective (algebraMap (ResidueField A) Fbar) :=
    (algebraMap (ResidueField A) Fbar).injective
  obtain ⟨c, hc⟩ := Infinite.exists_notMem_finset
    (({R₁.residue ⟨f, h₁⟩, R₂.residue ⟨f, h₂⟩} : Finset Fbar).preimage
      (algebraMap (ResidueField A) Fbar) hinj.injOn)
  have hc' : algebraMap (ResidueField A) Fbar c ∉ ({R₁.residue ⟨f, h₁⟩, R₂.residue ⟨f, h₂⟩} : Finset Fbar) :=
    fun h => hc (Finset.mem_preimage.mpr h)
  rw [Finset.mem_insert, Finset.mem_singleton, not_or] at hc'
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective c
  subst ha
  obtain ⟨g₁, e₁⟩ := regProl_residue_sub_algebraMap R₁ h₁ a
  obtain ⟨g₂, e₂⟩ := regProl_residue_sub_algebraMap R₂ h₂ a
  refine ⟨a, g₁, g₂, ?_, ?_, e₁, e₂⟩
  · rw [e₁]
    exact sub_ne_zero.mpr fun h => hc'.1 h.symm
  · rw [e₂]
    exact sub_ne_zero.mpr fun h => hc'.2 h.symm

private theorem riemannRochSpace_mono' {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    {E D : Divisor K₀ F₀} (h : ∀ W, E W ≤ D W) : riemannRochSpace E ≤ riemannRochSpace D := by
  intro f hf
  rw [mem_riemannRochSpace_iff] at hf ⊢
  intro W
  rcases hf W with h0 | hle
  · exact Or.inl h0
  · exact Or.inr (le_trans (neg_le_neg (h W)) hle)

end C3H

namespace C3H

private theorem mapDomain_filter_congr {X Y : Type*} (r : X → Y) (E : X →₀ ℤ) (p₁ p₂ : X → Prop)
    {d₁ : DecidablePred p₁} {d₂ : DecidablePred p₂} (v : Y) (h : ∀ V, r V = v → (p₁ V ↔ p₂ V)) :
    Finsupp.mapDomain r (E.filter p₁) v = Finsupp.mapDomain r (E.filter p₂) v := by
  classical
  have key : ∀ (p : X → Prop) (d : DecidablePred p) (a : X) (m : ℤ), r a ≠ v →
      Finsupp.mapDomain r (@Finsupp.filter X ℤ _ p d (Finsupp.single a m)) v = 0 := by
    intro p d a m hav
    by_cases hp : p a
    · rw [Finsupp.filter_single_of_pos p hp, Finsupp.mapDomain_single, Finsupp.single_apply,
        if_neg hav]
    · rw [Finsupp.filter_single_of_neg p hp, Finsupp.mapDomain_zero, Finsupp.zero_apply]
  induction E using Finsupp.induction_linear with
  | zero => rw [Finsupp.filter_zero, Finsupp.filter_zero]
  | add f₁ f₂ h₁ h₂ =>
    rw [Finsupp.filter_add, Finsupp.filter_add, Finsupp.mapDomain_add, Finsupp.mapDomain_add,
      Finsupp.add_apply, Finsupp.add_apply, h₁, h₂]
  | single a m =>
    by_cases hav : r a = v
    · by_cases hp : p₁ a
      · rw [Finsupp.filter_single_of_pos p₁ hp, Finsupp.filter_single_of_pos p₂ ((h a hav).mp hp)]
      · rw [Finsupp.filter_single_of_neg p₁ hp,
          Finsupp.filter_single_of_neg p₂ (fun h2 => hp ((h a hav).mpr h2))]
    · rw [key p₁ d₁ a m hav, key p₂ d₂ a m hav]

section Frame

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M} [NeZero (M / p)]
  {A : ValuationSubring (AlgebraicClosure ℚ)} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)}

private theorem hasPrincipalDivisors_FM : HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
  ModularCurve.hasPrincipalDivisors_xHFunctionFieldBar M H

private theorem aux_finiteDimensional_riemannRochSpace (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E) := by
  classical
  haveI : PerfectField (AlgebraicClosure ℚ) := PerfectField.ofCharZero
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := by
    apply ModularCurve.Gamma1_le_GammaH
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  have hj0 : jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) :=
    qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 _)
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ M (ModularCurve.jqModC_mem_full ℚ M))
  let y : ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hj0⟩
  have hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  have h := ModularCurve.transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) hT y hy
  obtain ⟨htr, hfd⟩ := h
  haveI := hfd
  haveI : Algebra.IsAlgebraic ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set _))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({y} : Set _))
      ↥(laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hne := AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional (AlgebraicClosure ℚ) y htr hfd
  haveI : Nonempty (Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := hne
  obtain ⟨hCO, hEFT⟩ := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H
  haveI := hCO
  haveI := hEFT
  haveI := AlgebraicCurve.finiteDimensional_lSpace_zero (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)
  exact AlgebraicCurve.finiteDimensional_lSpace E

variable (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
  (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (hα : α.IsIntegral) (hβ : β.IsIntegral)
  (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →
    Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))

private theorem neg_mass_le_ord_add_ord (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v)
    (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v)
    (f : ↥(xHFunctionFieldBar M H)) (hfV : f ∈ riemannRochSpace E)
    (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (hne₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0) (hne₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0) :
    -(Finsupp.mapDomain (Psp.reduceFst α hα) E v) ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
      + (δ ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) v)).ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hne₁ (by
      have h : (⟨(0 : ↥(xHFunctionFieldBar M H)), h₁⟩ : Rpd.R₁.integers) = 0 := rfl
      rw [h, map_zero])
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hasPrincipalDivisors_FM) f hf0
  have hlaw := hO f h₁ h₂ hne₁ hne₂ D hD v hv haff
  rw [← hlaw]
  have hDE : -E ≤ D := by
    intro W
    rw [Finsupp.coe_neg, Pi.neg_apply, hD W]
    exact ((mem_riemannRochSpace_iff.mp hfV) W).resolve_left hf0
  have hmono := Finsupp.le_def.mp (Finsupp.mapDomain_mono (f := Psp.reduceFst α hα) hDE) v
  have hneg : Finsupp.mapDomain (Psp.reduceFst α hα) (-E) = -Finsupp.mapDomain (Psp.reduceFst α hα) E :=
    map_neg (Finsupp.mapDomain.addMonoidHom (Psp.reduceFst α hα)) E
  rw [hneg] at hmono
  exact hmono

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
private theorem exists_orderBox_of_orderLawFixed (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE : ∀ W, 0 ≤ E W)
    [FiniteDimensional (AlgebraicClosure ℚ) ↥(riemannRochSpace E)]
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v)
    (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v) :
    ∃ s : ℤ, -(Finsupp.mapDomain (Psp.reduceFst α hα) E v) ≤ s ∧ s ≤ 0 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)), f ∈ riemannRochSpace E →
        ∀ (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
          (Rpd.R₁.residue ⟨f, h₁⟩ = 0 ∨ s ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
          (Rpd.R₂.residue ⟨f, h₂⟩ = 0 ∨
            -(Finsupp.mapDomain (Psp.reduceFst α hα) E v) - s ≤ (δ ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) v)).ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) := by
  classical
  haveI : Infinite (ResidueField ↥A) := inferInstance
  have hι : ∀ c, (RingHom.id (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c) = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c := fun _ => rfl
  haveI : FiniteDimensional (ResidueField ↥A)
      ↥(AlgebraicCurve.OrderBox.pairSpace Rpd.R₁ Rpd.R₂ (RingHom.id (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) hι (riemannRochSpace E)) :=
    AlgebraicCurve.OrderBox.finiteDimensional_pairSpace Rpd.R₁ Rpd.R₂ (RingHom.id (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) hι (riemannRochSpace E)
  have h1 : (1 : ↥(xHFunctionFieldBar M H)) ∈ riemannRochSpace E := by
    rw [mem_riemannRochSpace_iff]
    intro W
    right
    rw [Place.ord_one]
    have h := hE W
    omega
  obtain ⟨s, hs₁, hs₂, hall⟩ := AlgebraicCurve.OrderBox.exists_box_of_orderLaw (k := ResidueField ↥A) Rpd.R₁ Rpd.R₂
    (RingHom.id (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) hι (riemannRochSpace E) h1 v (δ ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) v))
    (Finsupp.mapDomain (Psp.reduceFst α hα) E v)
    (fun f hfV h₁ h₂ hne₁ hne₂ => neg_mass_le_ord_add_ord Psp Rpd α β hα hβ δ hO E v hv haff f hfV h₁ h₂ hne₁ hne₂)
  exact ⟨s, hs₁, hs₂, fun f hf h₁ h₂ => hall f hf h₁ h₂⟩

open Classical in
private theorem aux_image_fst_of_not_fixed (hDL : Rpd.DivisorLawFst α β hα hβ δ)
    {E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hE : ∀ W, 0 ≤ E W)
    {f : ↥(xHFunctionFieldBar M H)} (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v) :
    Rpd.R₁.residue ⟨f, h₁⟩ = 0 ∨
      -(Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ E) v) ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  by_cases h0 : Rpd.R₁.residue ⟨f, h₁⟩ = 0
  · exact Or.inl h0
  refine Or.inr ?_
  by_cases hlt : v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) < 0
  swap
  · push Not at hlt
    refine le_trans ?_ hlt
    rw [neg_nonpos]
    exact mapDomain_filter_nonneg (Psp.reduceFst α hα) E (Psp.IsStrictFst α β hα hβ δ) hE v
  obtain ⟨a, g₁, g₂, hne₁, hne₂, hr₁, -⟩ := regProl_exists_residue_sub_algebraMap_ne_zero Rpd.R₁ Rpd.R₂ h₁ h₂
  set g := f - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a
  have hg0 : g ≠ 0 := by
    intro h
    apply hne₁
    have e : (⟨g, g₁⟩ : Rpd.R₁.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  have hgE : g ∈ riemannRochSpace E :=
    sub_mem hf (algebraMap_mem_riemannRochSpace hE ((a : AlgebraicClosure ℚ)))
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hasPrincipalDivisors_FM) g hg0
  have hlaw := hDL g g₁ g₂ hne₁ hne₂ D hD v hv
  have hDE : ∀ W, -E W ≤ D W := fun W => by
    rw [hD W]
    exact ((mem_riemannRochSpace_iff.mp hgE) W).resolve_left hg0
  have hord : v.ord (Rpd.R₁.residue ⟨g, g₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) = v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
    rw [hr₁]
    exact ord_sub_algebraMap_of_ord_lt_zero v _ _ hlt
  rw [← hord, ← hlaw]
  exact neg_mapDomain_filter_le (Psp.reduceFst α hα) D E (Psp.IsStrictFst α β hα hβ δ) hDE v

open Classical in
private theorem aux_image_snd_of_not_fixed (hDL : Rpd.DivisorLawSnd α β hα hβ δ)
    {E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hE : ∀ W, 0 ≤ E W)
    {f : ↥(xHFunctionFieldBar M H)} (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hw : ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w) :
    Rpd.R₂.residue ⟨f, h₂⟩ = 0 ∨
      -(Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ E) w) ≤ w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  by_cases h0 : Rpd.R₂.residue ⟨f, h₂⟩ = 0
  · exact Or.inl h0
  refine Or.inr ?_
  by_cases hlt : w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) < 0
  swap
  · push Not at hlt
    refine le_trans ?_ hlt
    rw [neg_nonpos]
    exact mapDomain_filter_nonneg (Psp.reduceSnd β hβ δ) E (Psp.IsStrictSnd α β hα hβ δ) hE w
  obtain ⟨a, g₁, g₂, hne₁, hne₂, -, hr₂⟩ := regProl_exists_residue_sub_algebraMap_ne_zero Rpd.R₁ Rpd.R₂ h₁ h₂
  set g := f - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a
  have hg0 : g ≠ 0 := by
    intro h
    apply hne₂
    have e : (⟨g, g₂⟩ : Rpd.R₂.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  have hgE : g ∈ riemannRochSpace E :=
    sub_mem hf (algebraMap_mem_riemannRochSpace hE ((a : AlgebraicClosure ℚ)))
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hasPrincipalDivisors_FM) g hg0
  have hlaw := hDL g g₁ g₂ hne₁ hne₂ D hD w hw
  have hDE : ∀ W, -E W ≤ D W := fun W => by
    rw [hD W]
    exact ((mem_riemannRochSpace_iff.mp hgE) W).resolve_left hg0
  have hord : w.ord (Rpd.R₂.residue ⟨g, g₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) = w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
    rw [hr₂]
    exact ord_sub_algebraMap_of_ord_lt_zero w _ _ hlt
  rw [← hord, ← hlaw]
  exact neg_mapDomain_filter_le (Psp.reduceSnd β hβ δ) D E (Psp.IsStrictSnd α β hα hβ δ) hDE w

private theorem isCuspidal_of_not_isAffinePlace_reduceFst (hpM2 : ¬ p ^ 2 ∣ M) (hA : A.LiesOverPrime p)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hna : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V)) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V := by
  intro x hx a
  by_contra hpos
  push Not at hpos
  apply hna

  have hj0 : jqModC ℚ ∈ qExpFunctionFieldC ℚ (JHNeronObjectAtP.ΓN p M H hpM) :=
    qExpFunctionFieldC_mono ℚ (CohCarrier.GammaH_le_Gamma0 _)
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M / p) (ModularCurve.jqModC_mem_full ℚ (M / p)))
  let x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hj0⟩
  have hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
  have hxb0 : jqModC (ResidueField ↥A) ∈ qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) :=
    qExpFunctionFieldC_mono (ResidueField ↥A) (CohCarrier.GammaH_le_Gamma0 _)
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 (ResidueField ↥A) (M / p)
        (ModularCurve.jqModC_mem_full (ResidueField ↥A) (M / p)))
  let xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := ⟨jqModC (ResidueField ↥A), hxb0⟩
  have hαx : α x' = x := Subtype.ext ((hα_coe x').trans (hx'.trans hx.symm))

  have hup : 0 < (V.restrictAlong α hα).ord (x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) := by
    have h := Place.ord_restrictAlong α hα V (x' - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ))
    rw [map_sub, AlgHom.commutes, hαx] at h
    rw [h] at hpos
    exact pos_of_mul_pos_right hpos (Int.natCast_nonneg _)
  have hdown := ModularCurve.JHPlaceSpecialization.ord_pos_sp_sub_algebraMap_of_ord_pos p M H hpM hpM2 A hA Psp x' xb hx' rfl
    (V.restrictAlong α hα) a hup

  refine ⟨xb, IsLocalRing.residue ↥A a, rfl, ?_⟩
  set w := Psp.reduceFst α hα V with hw
  change 0 < w.ord (xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A a)) at hdown
  have hne : xb - algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (IsLocalRing.residue ↥A a) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hdown; exact lt_irrefl _ hdown
  have hmem := w.mem_of_ord_nonneg hne hdown.le
  have hxmem : (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ w.toValuationSubring := by
    have h := add_mem hmem (w.algebraMap_mem' (IsLocalRing.residue ↥A a))
    rwa [sub_add_cancel] at h
  refine ⟨hxmem, ?_⟩

  have hsplit : (⟨xb, hxmem⟩ : w.toValuationSubring)
      = ⟨_, hmem⟩ + ⟨_, w.algebraMap_mem' (IsLocalRing.residue ↥A a)⟩ := Subtype.ext (by simp)
  have hzero : IsLocalRing.residue w.toValuationSubring ⟨_, hmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (w.mem_maximalIdeal_iff_ord_pos hne hmem).mpr hdown
  rw [hsplit, map_add, hzero, zero_add]
  exact w.residue_algebraMap (IsLocalRing.residue ↥A a)

open Classical in
private theorem aux_cuspMass_fst_notZero (hpM2 : ¬ p ^ 2 ∣ M) (hA : A.LiesOverPrime p)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hna : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα c)) :
    Finsupp.mapDomain (Psp.reduceFst α hα)
        (E.filter (fun V => ¬ JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V)) (Psp.reduceFst α hα c)
      = Finsupp.mapDomain (Psp.reduceFst α hα)
        (E.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα c) := by
  refine mapDomain_filter_congr (Psp.reduceFst α hα) E _ _ (Psp.reduceFst α hα c) (fun V hV => ?_)
  have hVc : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V :=
    isCuspidal_of_not_isAffinePlace_reduceFst Psp α hα hpM2 hA hα_coe V (by rw [hV]; exact hna)
  constructor
  · intro hnz
    rcases ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA V hVc with h | h
    · exact h
    · exact absurd h hnz
  · intro hinf hz
    exact ModularCurve.JHPlaceSpecialization.not_isInftySide_of_isZeroSide p M H hpM A hA V hz hinf

open Classical in
private theorem aux_image_fst_cusp (hCL : Rpd.CuspLawInfty α hα) (hpM2 : ¬ p ^ 2 ∣ M) (hA : A.LiesOverPrime p)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    {E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hE : ∀ W, 0 ≤ E W)
    {f : ↥(xHFunctionFieldBar M H)} (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hna : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v)
    (hlift : ∃ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) c ∧ Psp.reduceFst α hα c = v) :
    Rpd.R₁.residue ⟨f, h₁⟩ = 0 ∨
      -(Finsupp.mapDomain (Psp.reduceFst α hα)
          (E.filter (fun V => ¬ JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V)) v)
        ≤ v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  by_cases h0 : Rpd.R₁.residue ⟨f, h₁⟩ = 0
  · exact Or.inl h0
  refine Or.inr ?_
  by_cases hlt : v.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) < 0
  swap
  · push Not at hlt
    refine le_trans ?_ hlt
    rw [neg_nonpos]
    exact mapDomain_filter_nonneg (Psp.reduceFst α hα) E _ hE v
  obtain ⟨c, hc, hcv⟩ := hlift
  subst hcv
  rw [aux_cuspMass_fst_notZero Psp α hα hpM2 hA hα_coe E c hna]
  obtain ⟨a, g₁, g₂, hne₁, hne₂, hr₁, -⟩ := regProl_exists_residue_sub_algebraMap_ne_zero Rpd.R₁ Rpd.R₂ h₁ h₂
  set g := f - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a
  have hg0 : g ≠ 0 := by
    intro h
    apply hne₁
    have e : (⟨g, g₁⟩ : Rpd.R₁.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  have hgE : g ∈ riemannRochSpace E :=
    sub_mem hf (algebraMap_mem_riemannRochSpace hE ((a : AlgebraicClosure ℚ)))
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hasPrincipalDivisors_FM) g hg0
  have hlaw := hCL g g₁ g₂ hne₁ hne₂ D hD c hc
  have hDE : ∀ W, -E W ≤ D W := fun W => by
    rw [hD W]
    exact ((mem_riemannRochSpace_iff.mp hgE) W).resolve_left hg0
  have hord : (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨g, g₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
      = (Psp.reduceFst α hα c).ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
    rw [hr₁]
    exact ord_sub_algebraMap_of_ord_lt_zero _ _ _ hlt
  rw [← hord, ← hlaw]
  exact neg_mapDomain_filter_le (Psp.reduceFst α hα) D E _ hDE (Psp.reduceFst α hα c)

open Classical in
private theorem aux_image_snd_cusp (hCL : Rpd.CuspLawZero β hβ δ)
    {E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)} (hE : ∀ W, 0 ≤ E W)
    {f : ↥(xHFunctionFieldBar M H)} (hf : f ∈ riemannRochSpace E)
    (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hlift : ∃ c : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) c ∧ Psp.reduceSnd β hβ δ c = w) :
    Rpd.R₂.residue ⟨f, h₂⟩ = 0 ∨
      -(Finsupp.mapDomain (Psp.reduceSnd β hβ δ)
          (E.filter (fun V => JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V)) w)
        ≤ w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
  by_cases h0 : Rpd.R₂.residue ⟨f, h₂⟩ = 0
  · exact Or.inl h0
  refine Or.inr ?_
  by_cases hlt : w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) < 0
  swap
  · push Not at hlt
    refine le_trans ?_ hlt
    rw [neg_nonpos]
    exact mapDomain_filter_nonneg (Psp.reduceSnd β hβ δ) E _ hE w
  obtain ⟨c, hc, hcw⟩ := hlift
  subst hcw
  obtain ⟨a, g₁, g₂, hne₁, hne₂, -, hr₂⟩ := regProl_exists_residue_sub_algebraMap_ne_zero Rpd.R₁ Rpd.R₂ h₁ h₂
  set g := f - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a
  have hg0 : g ≠ 0 := by
    intro h
    apply hne₂
    have e : (⟨g, g₂⟩ : Rpd.R₂.integers) = 0 := Subtype.ext h
    rw [e, map_zero]
  have hgE : g ∈ riemannRochSpace E :=
    sub_mem hf (algebraMap_mem_riemannRochSpace hE ((a : AlgebraicClosure ℚ)))
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (self := hasPrincipalDivisors_FM) g hg0
  have hlaw := hCL g g₁ g₂ hne₁ hne₂ D hD c hc
  have hDE : ∀ W, -E W ≤ D W := fun W => by
    rw [hD W]
    exact ((mem_riemannRochSpace_iff.mp hgE) W).resolve_left hg0
  have hord : (Psp.reduceSnd β hβ δ c).ord (Rpd.R₂.residue ⟨g, g₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
      = (Psp.reduceSnd β hβ δ c).ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) := by
    rw [hr₂]
    exact ord_sub_algebraMap_of_ord_lt_zero _ _ _ hlt
  rw [← hord, ← hlaw]
  exact neg_mapDomain_filter_le (Psp.reduceSnd β hβ δ) D E _ hDE (Psp.reduceSnd β hβ δ c)

end Frame
end C3H

namespace C3H

theorem not_dvd_div_of_not_sq_dvd {p M : ℕ} (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) : ¬ p ∣ M / p := by
  rintro ⟨c, hc⟩
  apply hpM2
  refine ⟨c, ?_⟩
  calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
    _ = p * (p * c) := by rw [hc]
    _ = p ^ 2 * c := by ring

set_option maxHeartbeats 1600000 in

theorem delta_comm (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (hpN : ¬ p ∣ M / p) (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) →
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • v)
    (x : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) :
    δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p x)
      = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ x) := by
  rw [hδ, hδ, ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
    (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) x]

end C3H

open Classical in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hE : ∀ V, 0 ≤ E V)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ riemannRochSpace E) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers) :
    (∀ (D₁ : Divisor (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))), (∀ w, 0 ≤ D₁ w) →
      (∀ w, ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ E) w ≤ D₁ w) →
      (∀ w, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) w →
        Finsupp.mapDomain (Psp.reduceFst α hα) (E.filter (fun V => ¬ JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V)) w ≤ D₁ w) →
      (∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → Finsupp.mapDomain (Psp.reduceFst α hα) E v ≤ D₁ v) →
      ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Rpd.R₁.residue ⟨f, h₁⟩ = 0 ∨ -D₁ w ≤ w.ord (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
    (∀ (D₂ : Divisor (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))), (∀ w, 0 ≤ D₂ w) →
      (∀ w, ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ E) w ≤ D₂ w) →
      (∀ w, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w) →
        Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (E.filter (fun V => JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V)) w ≤ D₂ w) →
      (∀ v, JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v → JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v → Finsupp.mapDomain (Psp.reduceFst α hα) E v ≤ D₂ (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p v))) →
      ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Rpd.R₂.residue ⟨f, h₂⟩ = 0 ∨ -D₂ w ≤ w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
    (∀ s ∈ SS, (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = s.1 → 0 ≤ V.ord f) →
      ∃ c : (ResidueField ↥A), s.1.HasValue (Rpd.R₁.residue ⟨f, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) c ∧ s.2.HasValue (Rpd.R₂.residue ⟨f, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) c) := by

  clear hLFst hLSnd hUnit hNV hTD hFix hθgal hβθ hβ_coe hHp hSS

  have hcomm := C3H.delta_comm p M H hpM A (C3H.not_dvd_div_of_not_sq_dvd hpM hpM2) pb δ hδ
  haveI := C3H.aux_finiteDimensional_riemannRochSpace (M := M) (H := H) E
  refine ⟨?_, ?_, ?_⟩
  · intro D₁ hD₁ hstrict hcuspD haffmass w
    by_cases hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w
    · by_cases haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) w
      · obtain ⟨s, hs₁, hs₂, hs⟩ := C3H.exists_orderBox_of_orderLawFixed Psp Rpd α β hα hβ δ hO E hE w hfix haff
        have hm := haffmass w hfix haff
        rcases (hs f hf h₁ h₂).1 with h0 | hb
        · exact Or.inl h0
        · right
          omega
      · rcases C3H.aux_image_fst_cusp Psp Rpd α hα hmodel.2.2.1 hpM2 hA hα_coe hE hf h₁ h₂ w haff (hcusp w haff).1 with h0 | hb
        · exact Or.inl h0
        · right
          have := hcuspD w hfix haff
          omega
    · rcases C3H.aux_image_fst_of_not_fixed Psp Rpd α β hα hβ δ hmodel.1 hE hf h₁ h₂ w hfix with h0 | hb
      · exact Or.inl h0
      · right
        have := hstrict w hfix
        omega
  · intro D₂ hD₂ hstrict hcuspD haffmass w
    by_cases hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ w
    · by_cases haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) w)
      ·
        have hvw : δ ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) w)) = w := by
          rw [hcomm]; exact hfix
        have hvfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) w) := by
          show (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) (δ ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) w))) = (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) w
          rw [hvw]
        obtain ⟨s, hs₁, hs₂, hs⟩ := C3H.exists_orderBox_of_orderLawFixed Psp Rpd α β hα hβ δ hO E hE ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) w) hvfix haff
        have hm := haffmass _ hvfix haff
        rw [hvw] at hm
        rcases (hs f hf h₁ h₂).2 with h0 | hb
        · exact Or.inl h0
        · right
          rw [hvw] at hb
          omega
      · have hnaw : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) w := fun h =>
          haff ((ModularCurve.JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
            p M H hpM A hA).1 w h)
        rcases C3H.aux_image_snd_cusp Psp Rpd β hβ δ hmodel.2.2.2 hE hf h₁ h₂ w (hcusp w hnaw).2 with h0 | hb
        · exact Or.inl h0
        · right
          have := hcuspD w hfix haff
          omega
    · rcases C3H.aux_image_snd_of_not_fixed Psp Rpd α β hα hβ δ hmodel.2.1 hE hf h₁ h₂ w hfix with h0 | hb
      · exact Or.inl h0
      · right
        have := hstrict w hfix
        omega
  · exact fun s hs hreg => hRL.2 f h₁ h₂ s hs hreg

end

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residue_fst_box_and_residue_snd_box_and_node_hasValue_of_mem_riemannRochSpace (solution)
