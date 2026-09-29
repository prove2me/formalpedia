-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.exists_sub_algebraMap_forall_ord_pos_reduceFst_notMem_of_fixed_of_isAffinePlace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/72918f49-04f9-54aa-ad24-2290f64e0058

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isInftySide_or_isZeroSide_of_isCuspidal
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_pos_sp_sub_algebraMap_of_ord_pos
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isCuspidal_of_isCuspidalPrime
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_AlgebraicCurve_Place_hasValue_iff_mem_and_eq_or_ord_sub_pos
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_sub_algebraMap_forall_ord_pos_reduceFst_notMem_of_fixed_of_isAffinePlace
p2m_attr_erase "instance" "ValuationSubring.instIsAlgClosedResidueField ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups Classical

namespace SkitFixedAux

section Generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
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

theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem mem_maximalIdeal_of_ord_pos {f : F} (h : 0 < v.ord f) :
    ∃ hf : f ∈ v.toValuationSubring, (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp at h
  refine ⟨mem_of_ord_nonneg v hf0 h.le, ?_⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have := v.ord_coe_unit hu.unit
  rw [IsUnit.unit_spec] at this
  simp only at this
  omega

theorem ord_algebraMap_eq_zero (a : K) : v.ord (algebraMap K F a) = 0 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hu : IsUnit (algebraMap K v.toValuationSubring a) := ha.isUnit.map _
    have h := v.ord_coe_unit hu.unit
    rwa [IsUnit.unit_spec, Place.coe_algebraMap] at h

theorem ord_sub_algebraMap_of_neg {g : F} (hg : v.ord g < 0) (a : K) :
    v.ord (g - algebraMap K F a) = v.ord g := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hg0 : g ≠ 0 := by rintro rfl; simp at hg
  have ha0 : algebraMap K F a ≠ 0 := (map_ne_zero _).mpr ha

  have hx : 0 < v.ord (algebraMap K F a / g) := by
    rw [div_eq_mul_inv, v.ord_mul ha0 (inv_ne_zero hg0), v.ord_inv, ord_algebraMap_eq_zero]; omega
  obtain ⟨hxmem, hxmax⟩ := mem_maximalIdeal_of_ord_pos v hx
  have hunit : IsUnit (1 - (⟨_, hxmem⟩ : v.toValuationSubring)) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hxmax
  have heq : g - algebraMap K F a = g * ((hunit.unit : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    push_cast
    field_simp
  rw [heq, v.ord_mul hg0, v.ord_coe_unit, add_zero]
  intro h0
  exact hunit.ne_zero (Subtype.ext h0)

theorem eq_of_ord_sub_algebraMap_pos {x : F} {a a' : K}
    (h : 0 < v.ord (x - algebraMap K F a)) (h' : 0 < v.ord (x - algebraMap K F a')) : a = a' := by
  by_contra hne
  obtain ⟨hm, hmax⟩ := mem_maximalIdeal_of_ord_pos v h
  obtain ⟨hm', hmax'⟩ := mem_maximalIdeal_of_ord_pos v h'
  have hd := sub_mem hmax' hmax
  have : (⟨x - algebraMap K F a', hm'⟩ : v.toValuationSubring) - ⟨x - algebraMap K F a, hm⟩ =
      algebraMap K v.toValuationSubring (a - a') := by
    apply Subtype.ext; rw [Place.coe_algebraMap, map_sub, AddSubgroupClass.coe_sub]; ring
  rw [this] at hd
  exact (IsLocalRing.mem_maximalIdeal _).mp hd ((sub_ne_zero.mpr hne).isUnit.map _)

end Generic

section Fibre
variable {X Y : Type*} (r : X → Y) (D : X →₀ ℤ) (v : Y)

theorem mapDomain_apply_eq_sum : Finsupp.mapDomain r D v = ∑ W ∈ D.support, if r W = v then D W else 0 := by
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]

theorem mapDomain_nonneg (h : ∀ W, r W = v → 0 ≤ D W) : 0 ≤ Finsupp.mapDomain r D v := by
  rw [mapDomain_apply_eq_sum]
  exact Finset.sum_nonneg fun W _ => by split_ifs with hW; exacts [h W hW, le_refl _]

theorem mapDomain_eq_add_single (V : X) (hV : r V = v) :
    Finsupp.mapDomain r D v = Finsupp.mapDomain r (D - Finsupp.single V (D V)) v + D V := by
  have hsplit : D = (D - Finsupp.single V (D V)) + Finsupp.single V (D V) := by simp
  conv_lhs => rw [hsplit]
  rw [Finsupp.mapDomain_add, Finsupp.add_apply, Finsupp.mapDomain_single, Finsupp.single_apply, if_pos hV]

theorem le_mapDomain (V : X) (hV : r V = v) (h : ∀ W, r W = v → W ≠ V → 0 ≤ D W) :
    D V ≤ Finsupp.mapDomain r D v := by
  have h0 : 0 ≤ Finsupp.mapDomain r (D - Finsupp.single V (D V)) v := by
    apply mapDomain_nonneg
    intro W hW
    by_cases hWV : W = V
    · subst hWV; simp
    · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hWV), sub_zero]
      exact h W hW hWV
  rw [mapDomain_eq_add_single r D v V hV]
  omega

theorem add_le_mapDomain (V V₀ : X) (hne : V ≠ V₀) (hV : r V = v) (hV₀ : r V₀ = v)
    (h : ∀ W, r W = v → W ≠ V → W ≠ V₀ → 0 ≤ D W) :
    D V + D V₀ ≤ Finsupp.mapDomain r D v := by
  have h1 : (D - Finsupp.single V₀ (D V₀)) V ≤ Finsupp.mapDomain r (D - Finsupp.single V₀ (D V₀)) v := by
    apply le_mapDomain r _ v V hV
    intro W hW hWV
    by_cases hW0 : W = V₀
    · subst hW0; simp
    · simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hW0), sub_zero]
      exact h W hW hWV hW0
  have hVval : (D - Finsupp.single V₀ (D V₀)) V = D V := by
    simp only [Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply, if_neg (Ne.symm hne), sub_zero]
  rw [hVval] at h1
  rw [mapDomain_eq_add_single r D v V₀ hV₀]
  omega

end Fibre

end SkitFixedAux

namespace SkitFixedAux

section Frame

variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
  (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

include hpM2 in
theorem comm_of_pin (pb : (ZMod (M / p))ˣ) (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w) := by
  have hpN : ¬ p ∣ M / p := by
    rintro ⟨k, hk⟩; apply hpM2; exact ⟨k, by rw [pow_two, mul_assoc, ← hk, Nat.mul_div_cancel' hpM]⟩
  rw [hδ, hδ]
  exact ModularCurve.qExpFrobeniusPlaceModL_ofAlgAut_diamondActionModL_smul (ResidueField ↥A) p (M / p) hpN
    (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb) w

variable (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hcomm : ∀ w, qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (δ w) = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w))

include hcomm in
theorem fixed_frob_iff (y : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y) ↔ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y := by
  have hinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1
  unfold JHPlaceSpecialization.Fixed
  constructor
  · intro h
    rw [hcomm]
    exact hinj h
  · intro hy
    rw [← hcomm, ← hcomm, hcomm, hy]

include hcomm in
theorem fixed_delta_frob (y : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hy : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ y) : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p y)) := by
  unfold JHPlaceSpecialization.Fixed at hy ⊢
  rw [hy, hcomm]

end Frame

end SkitFixedAux

namespace SkitFixedAux

theorem case_strictFst
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hq : ∀ W, q W = W.ord f)
    (hpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), q W < 0 → W = V₀ ∨ (Psp.reduceFst α hα W ∉ B ∧ Psp.reduceSnd β hβ δ W ∉ B))
    (hF₁ : ∀ w ∈ B, ¬ 0 < w.ord (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hF₂ : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w ∈ B ∨ ∃ b ∈ B, w = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p b)) → ¬ 0 < w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hVne : V ≠ V₀) (hzero : 0 < q V)
    (hfix₀ : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V₀))
    (hDLF : Rpd.DivisorLawFst α β hα hβ δ)
    (hV : Psp.IsStrictFst α β hα hβ δ V) (hB : Psp.reduceFst α hα V ∈ B) : False := by
  have hlaw := hDLF f h₁ h₂ hr₁ hr₂ q hq (Psp.reduceFst α hα V) hV.2

  have hle : (Psp.fstDiv α β hα hβ δ q) V ≤ Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ q) (Psp.reduceFst α hα V) := by
    apply le_mapDomain _ _ _ V rfl
    intro W hW hWV
    unfold JHPlaceSpecialization.fstDiv
    rw [Finsupp.filter_apply]
    split_ifs with hsW
    · by_contra hneg
      rcases hpoles W (lt_of_not_ge hneg) with rfl | ⟨h1, -⟩
      · exact hV.2 (hW ▸ hfix₀)
      · exact h1 (hW ▸ hB)
    · exact le_refl _
  have hVval : (Psp.fstDiv α β hα hβ δ q) V = q V := by
    unfold JHPlaceSpecialization.fstDiv; rw [Finsupp.filter_apply, if_pos hV]
  rw [hVval, hlaw] at hle
  exact hF₁ _ hB (lt_of_lt_of_le hzero hle)

theorem case_strictSnd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hq : ∀ W, q W = W.ord f)
    (hpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), q W < 0 → W = V₀ ∨ (Psp.reduceFst α hα W ∉ B ∧ Psp.reduceSnd β hβ δ W ∉ B))
    (hF₁ : ∀ w ∈ B, ¬ 0 < w.ord (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hF₂ : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w ∈ B ∨ ∃ b ∈ B, w = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p b)) → ¬ 0 < w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hVne : V ≠ V₀) (hzero : 0 < q V)
    (hfix₂ : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd β hβ δ V₀))
    (hDLS : Rpd.DivisorLawSnd α β hα hβ δ)
    (hV : Psp.IsStrictSnd α β hα hβ δ V) (hB : Psp.reduceFst α hα V ∈ B) : False := by
  have hlaw := hDLS f h₁ h₂ hr₁ hr₂ q hq (Psp.reduceSnd β hβ δ V) hV.2
  have hle : (Psp.sndDiv α β hα hβ δ q) V ≤ Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ q) (Psp.reduceSnd β hβ δ V) := by
    apply le_mapDomain _ _ _ V rfl
    intro W hW hWV
    unfold JHPlaceSpecialization.sndDiv
    rw [Finsupp.filter_apply]
    split_ifs with hsW
    · by_contra hneg
      rcases hpoles W (lt_of_not_ge hneg) with rfl | ⟨h1, -⟩
      · exact hV.2 (hW ▸ hfix₂)
      · apply h1
        rw [hsW.1, hW, ← hV.1]; exact hB
    · exact le_refl _
  have hVval : (Psp.sndDiv α β hα hβ δ q) V = q V := by
    unfold JHPlaceSpecialization.sndDiv; rw [Finsupp.filter_apply, if_pos hV]
  rw [hVval, hlaw] at hle
  refine hF₂ _ (Or.inl ?_) (lt_of_lt_of_le hzero hle)
  rw [← hV.1]; exact hB

theorem case_fixed
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hq : ∀ W, q W = W.ord f)
    (hpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), q W < 0 → W = V₀ ∨ (Psp.reduceFst α hα W ∉ B ∧ Psp.reduceSnd β hβ δ W ∉ B))
    (hF₁ : ∀ w ∈ B, ¬ 0 < w.ord (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hF₂ : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w ∈ B ∨ ∃ b ∈ B, w = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p b)) → ¬ 0 < w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hVne : V ≠ V₀) (hzero : 0 < q V)
    (hO : Rpd.OrderLawFixed α β hα hβ δ) (hqV₀ : q V₀ = -1)
    (hres : Psp.reduceFst α hα V₀ ∈ B →
      ((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = -1 ∨
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V₀))).ord (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = -1))
    (hfixV : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V)) (haffV : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V))
    (hB : Psp.reduceFst α hα V ∈ B) : False := by
  have hlaw := hO f h₁ h₂ hr₁ hr₂ q hq (Psp.reduceFst α hα V) hfixV haffV
  have hR₁ := hF₁ _ hB
  have hR₂ := hF₂ (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V))) (Or.inr ⟨_, hB, rfl⟩)
  by_cases h0 : Psp.reduceFst α hα V₀ = Psp.reduceFst α hα V
  ·
    have hle : q V + q V₀ ≤ Finsupp.mapDomain (Psp.reduceFst α hα) q (Psp.reduceFst α hα V) := by
      apply add_le_mapDomain _ _ _ V V₀ hVne rfl h0
      intro W hW hWV hWV₀
      by_contra hneg
      rcases hpoles W (lt_of_not_ge hneg) with rfl | ⟨h1, -⟩
      · exact hWV₀ rfl
      · exact h1 (hW ▸ hB)
    rw [hlaw, hqV₀] at hle
    have hres' := hres (h0 ▸ hB)
    rw [h0] at hres'
    rcases hres' with e1 | e2
    · rw [e1] at hle; omega
    · rw [e2] at hle; omega
  · have hle : q V ≤ Finsupp.mapDomain (Psp.reduceFst α hα) q (Psp.reduceFst α hα V) := by
      apply le_mapDomain _ _ _ V rfl
      intro W hW hWV
      by_contra hneg
      rcases hpoles W (lt_of_not_ge hneg) with rfl | ⟨h1, -⟩
      · exact h0 hW
      · exact h1 (hW ▸ hB)
    rw [hlaw] at hle
    omega

theorem case_infty
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hq : ∀ W, q W = W.ord f)
    (hpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), q W < 0 → W = V₀ ∨ (Psp.reduceFst α hα W ∉ B ∧ Psp.reduceSnd β hβ δ W ∉ B))
    (hF₁ : ∀ w ∈ B, ¬ 0 < w.ord (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hF₂ : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w ∈ B ∨ ∃ b ∈ B, w = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p b)) → ¬ 0 < w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hVne : V ≠ V₀) (hzero : 0 < q V)
    (hnc₀ : ¬ JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V₀)
    (hCLI : Rpd.CuspLawInfty α hα)
    (hV : JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) V) (hB : Psp.reduceFst α hα V ∈ B) : False := by
  have hlaw := hCLI f h₁ h₂ hr₁ hr₂ q hq V hV
  have hle : (q.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) V ≤
      Finsupp.mapDomain (Psp.reduceFst α hα) (q.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα V) := by
    apply le_mapDomain _ _ _ V rfl
    intro W hW hWV
    rw [Finsupp.filter_apply]
    split_ifs with hsW
    · by_contra hneg
      rcases hpoles W (lt_of_not_ge hneg) with rfl | ⟨h1, -⟩
      · exact hnc₀ hsW.1
      · exact h1 (hW ▸ hB)
    · exact le_refl _
  have hVval : (q.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) V = q V := by
    rw [Finsupp.filter_apply, if_pos hV]
  rw [hVval, hlaw] at hle
  exact hF₁ _ hB (lt_of_lt_of_le hzero hle)

theorem case_zero
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))

    (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers)
    (hr₁ : Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0) (hr₂ : Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0)
    (q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hq : ∀ W, q W = W.ord f)
    (hpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), q W < 0 → W = V₀ ∨ (Psp.reduceFst α hα W ∉ B ∧ Psp.reduceSnd β hβ δ W ∉ B))
    (hF₁ : ∀ w ∈ B, ¬ 0 < w.ord (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hF₂ : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w ∈ B ∨ ∃ b ∈ B, w = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p b)) → ¬ 0 < w.ord (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hVne : V ≠ V₀) (hzero : 0 < q V)
    (hnc₀ : ¬ JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) V₀)
    (hCLZ : Rpd.CuspLawZero β hβ δ)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ C))
    (hV : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) V) (hB : Psp.reduceFst α hα V ∈ B) : False := by
  have hlaw := hCLZ f h₁ h₂ hr₁ hr₂ q hq V hV
  have hle : (q.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) V ≤
      Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (q.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ V) := by
    apply le_mapDomain _ _ _ V rfl
    intro W hW hWV
    rw [Finsupp.filter_apply]
    split_ifs with hsW
    · by_contra hneg
      rcases hpoles W (lt_of_not_ge hneg) with rfl | ⟨h1, -⟩
      · exact hnc₀ hsW.1
      · apply h1
        rw [horient0 W hsW, hW, ← horient0 V hV]; exact hB
    · exact le_refl _
  have hVval : (q.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) V = q V := by
    rw [Finsupp.filter_apply, if_pos hV]
  rw [hVval, hlaw] at hle
  refine hF₂ _ (Or.inl ?_) (lt_of_lt_of_le hzero hle)
  rw [← horient0 V hV]; exact hB

end SkitFixedAux

namespace SkitFixedAux

theorem shift_mem {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] (R : RegularProlongation A F Fbar)
    {g : F} (hg : g ∈ R.integers) (c : ↥A) :
    ∃ h : g - algebraMap L F (c : L) ∈ R.integers,
      R.residue ⟨_, h⟩ = R.residue ⟨g, hg⟩ - algebraMap (ResidueField A) Fbar (IsLocalRing.residue A c) := by
  have hc : algebraMap L F (c : L) ∈ R.integers := (R.algebraMap_mem_iff (c : L)).mpr c.2
  refine ⟨sub_mem hg hc, ?_⟩
  have : (⟨g - algebraMap L F (c : L), sub_mem hg hc⟩ : ↥R.integers) = ⟨g, hg⟩ - ⟨_, hc⟩ := rfl
  rw [this, map_sub, R.residue_algebraMap]

theorem jqModC_mem_xHFunctionFieldBar (N : ℕ) (H' : Subgroup (ZMod N)ˣ) :
    jqModC (AlgebraicClosure ℚ) ∈ xHFunctionFieldBar N H' := by
  have hjq : jq ∈ xHFunctionField N H' := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH N H')
    exact intFormRatiosC_subset ℚ _ (jqModC_mem_intFormRatiosC ℚ _)
  have h := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hjq
  have hcoe : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := by
    show (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)
    exact map_jqModC _
  rw [hcoe] at h
  exact h

theorem jqModC_mem_Fbar (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (κ : Type) [Field κ] :
    jqModC κ ∈ qExpFunctionFieldC κ (JHNeronObjectAtP.ΓN p M H hpM) :=
  intFormRatiosC_subset κ _ (jqModC_mem_intFormRatiosC κ _)

section Cores
variable (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (Psp : JHPlaceSpecialization p M H hpM A)

include hpM2 hA hα_coe in

theorem isCuspidal_of_not_isAffinePlace (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hW : ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα W)) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W := by
  intro x hx a
  by_contra hlt
  have hlt' : 0 < W.ord (x - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) := lt_of_not_ge hlt
  apply hW
  set x₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_xHFunctionFieldBar (M / p) _⟩ with hx₀
  let xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) := ⟨_, jqModC_mem_Fbar p M H hpM (ResidueField ↥A)⟩
  have hxeq : x = α x₀ := Subtype.ext (by rw [hα_coe, hx])
  have h1 : 0 < W.ord (α (x₀ - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ))) := by
    rw [map_sub, AlgHom.commutes, ← hxeq]; exact hlt'
  rw [Place.ord_restrictAlong α hα W] at h1
  have h3 := ModularCurve.JHPlaceSpecialization.ord_pos_sp_sub_algebraMap_of_ord_pos p M H hpM hpM2 A hA Psp x₀ xb rfl rfl _ a
    (pos_of_mul_pos_right h1 (Int.natCast_nonneg _))
  refine ⟨xb, IsLocalRing.residue ↥A a, rfl, ?_⟩
  rw [Place.hasValue_iff_mem_and_eq_or_ord_sub_pos]
  refine ⟨?_, Or.inr h3⟩
  have hne : (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) - algebraMap (ResidueField ↥A) _ (IsLocalRing.residue ↥A a) ≠ 0 := by
    intro h0; rw [h0] at h3; simp at h3
  have hmem := mem_of_ord_nonneg _ hne h3.le
  have := add_mem hmem ((Psp.sp (W.restrictAlong α hα)).algebraMap_mem' (IsLocalRing.residue ↥A a))
  simp at this
  exact this

include hpM2 hA hα_coe in

theorem not_isAffinePlace_of_isCuspidal (W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hc : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) W) :
    ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα W) := by
  set x₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ⟨jqModC (AlgebraicClosure ℚ), jqModC_mem_xHFunctionFieldBar (M / p) _⟩ with hx₀
  let xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) := ⟨_, jqModC_mem_Fbar p M H hpM (ResidueField ↥A)⟩
  have hepos : 0 < Place.ramificationIndexAlong α W := by
    letI := AlgebraicCurve.algebraAlong α
    haveI := AlgebraicCurve.isScalarTower_along α
    haveI := AlgebraicCurve.isIntegral_along α hα
    exact Place.ramificationIndex_pos (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) W
  have hpole : ∀ a : ↥A, (W.restrictAlong α hα).ord (x₀ - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have h1 := hc (α x₀) (by rw [hα_coe]) a
    rw [← AlgHom.commutes α, ← map_sub, Place.ord_restrictAlong α hα W] at h1
    have he : (0 : ℤ) < (Place.ramificationIndexAlong α W : ℤ) := by exact_mod_cast hepos
    by_contra hlt
    exact absurd h1 (not_le.mpr (mul_pos he (lt_of_not_ge hlt)))
  have hneg := ModularCurve.JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le p M H hpM hpM2 A hA Psp x₀ xb rfl rfl _ hpole
  rintro ⟨x, a, hx, hval⟩
  have hxx : x = xb := Subtype.ext hx
  have h0 := ord_nonneg_of_mem _ hval.mem
  rw [hxx] at h0
  exact absurd hneg (not_lt.mpr h0)

end Cores

end SkitFixedAux

namespace SkitFixedAux

theorem exists_good_constant {K F : Type*} [Field K] [Field F] [Algebra K F] [Infinite K]
    (r₁ r₂ : F) (S₁ S₂ : Set (Place K F)) (hS₁ : S₁.Finite) (hS₂ : S₂.Finite) :
    ∃ cb : K, r₁ ≠ algebraMap K F cb ∧ r₂ ≠ algebraMap K F cb ∧
      (∀ w ∈ S₁, ¬ 0 < w.ord (r₁ - algebraMap K F cb)) ∧ (∀ w ∈ S₂, ¬ 0 < w.ord (r₂ - algebraMap K F cb)) := by
  let Bad : Set K := {a | r₁ = algebraMap K F a} ∪ {a | r₂ = algebraMap K F a} ∪
    (⋃ w ∈ S₁, {a | 0 < w.ord (r₁ - algebraMap K F a)}) ∪ (⋃ w ∈ S₂, {a | 0 < w.ord (r₂ - algebraMap K F a)})
  have hsub : ∀ r : F, ({a : K | r = algebraMap K F a}).Subsingleton := fun r a ha b hb =>
    (algebraMap K F).injective (ha.symm.trans hb)
  have hsub' : ∀ (r : F) (w : Place K F), ({a : K | 0 < w.ord (r - algebraMap K F a)}).Subsingleton :=
    fun r w a ha b hb => eq_of_ord_sub_algebraMap_pos w ha hb
  have hfin : Bad.Finite := by
    refine Set.Finite.union (Set.Finite.union (Set.Finite.union (hsub r₁).finite (hsub r₂).finite) ?_) ?_
    · exact hS₁.biUnion fun w _ => (hsub' r₁ w).finite
    · exact hS₂.biUnion fun w _ => (hsub' r₂ w).finite
  obtain ⟨cb, hcb⟩ := Set.Finite.exists_notMem hfin
  refine ⟨cb, fun h => hcb ?_, fun h => hcb ?_, fun w hw h => hcb ?_, fun w hw h => hcb ?_⟩
  · exact Or.inl (Or.inl (Or.inl h))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr (Set.mem_biUnion hw h))
  · exact Or.inr (Set.mem_biUnion hw h)

end SkitFixedAux

set_option maxHeartbeats 1600000 in

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
    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd β hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ C))

    (B : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (V₀ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hfix : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V₀))
    (haff : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V₀))
    (hord : ∀ s ∈ SS, Psp.reduceFst α hα V₀ ≠ s.1 ∧ Psp.reduceFst α hα V₀ ≠ s.2)

    (g : ↥(xHFunctionFieldBar M H)) (h₁ : g ∈ Rpd.R₁.integers) (h₂ : g ∈ Rpd.R₂.integers)
    (hg₁ : Rpd.R₁.residue ⟨g, h₁⟩ ≠ 0) (hg₂ : Rpd.R₂.residue ⟨g, h₂⟩ ≠ 0)
    (hpole : V₀.ord g = -1)
    (hother : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V ≠ V₀ → V.ord g < 0 → Psp.reduceFst α hα V ∉ B ∧ Psp.reduceSnd β hβ δ V ∉ B)
    (hres : ((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨g, h₁⟩) = -1 ∧
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V₀))).ord (Rpd.R₂.residue ⟨g, h₂⟩) = 0) ∨
      ((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨g, h₁⟩) = 0 ∧
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V₀))).ord (Rpd.R₂.residue ⟨g, h₂⟩) = -1)) :
    ∃ (c : ↥A) (h₁' : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ) ∈ Rpd.R₁.integers) (h₂' : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ) ∈ Rpd.R₂.integers),
      Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₁'⟩ ≠ 0 ∧ Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₂'⟩ ≠ 0 ∧
      V₀.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) = -1 ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) < 0 → V.ord g < 0) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V ≠ V₀ → 0 < V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) → Psp.reduceFst α hα V ∉ B) ∧
      ∃ q : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (∀ V, q V = V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ))) ∧ Divisor.degree q = 0 := by
  clear hLFst hLSnd hUnit hcusp hRL hNV hθgal hβθ hβ_coe hFix hord horientInf
  have hcomm := SkitFixedAux.comm_of_pin p M H hpM hpM2 A pb δ hδ
  clear hδ hpb
  obtain ⟨hDLF, hDLS, hCLI, hCLZ⟩ := hmodel

  have hfix₂ : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd β hβ δ V₀) := by
    rcases hTD V₀ with hsnd | hfst
    · exact (SkitFixedAux.fixed_frob_iff p M H hpM A δ hcomm _).mp (hsnd ▸ hfix)
    · exact hfst ▸ SkitFixedAux.fixed_delta_frob p M H hpM A δ hcomm _ hfix

  have hnc₀ : ¬ JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V₀ := fun hc =>
    SkitFixedAux.not_isAffinePlace_of_isCuspidal p M H hpM hpM2 A hA α hα_coe hα Psp V₀ hc haff
  have hnc₀' : ¬ JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) V₀ := fun hc =>
    hnc₀ (ModularCurve.JHPlaceSpecialization.isCuspidal_of_isCuspidalPrime p M H hpM A hA V₀ hc)

  have hinj := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1
  have hS₂fin : ((qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) ⁻¹' (B : Set (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∪ (fun b => δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p b)) '' (B : Set (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))).Finite :=
    (B.finite_toSet.preimage hinj.injOn).union (B.finite_toSet.image _)
  obtain ⟨cb, hne₁, hne₂, hF₁, hF₂⟩ := SkitFixedAux.exists_good_constant
    (Rpd.R₁.residue ⟨g, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (Rpd.R₂.residue ⟨g, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (B : Set (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) _ B.finite_toSet hS₂fin
  obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective cb
  change IsLocalRing.residue ↥A c = cb at hc

  obtain ⟨h₁', hr₁⟩ := SkitFixedAux.shift_mem Rpd.R₁ h₁ c
  obtain ⟨h₂', hr₂⟩ := SkitFixedAux.shift_mem Rpd.R₂ h₂ c
  rw [hc] at hr₁ hr₂
  have hr₁ne : Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₁'⟩ ≠ 0 := by
    rw [hr₁, sub_ne_zero]; exact fun h => hne₁ (Subtype.ext (congrArg Subtype.val h))
  have hr₂ne : Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₂'⟩ ≠ 0 := by
    rw [hr₂, sub_ne_zero]; exact fun h => hne₂ (Subtype.ext (congrArg Subtype.val h))
  have hordV₀ : V₀.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) = -1 := by
    rw [SkitFixedAux.ord_sub_algebraMap_of_neg V₀ (by rw [hpole]; norm_num), hpole]
  have hgc0 : g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ) ≠ 0 := by intro h0; rw [h0] at hordV₀; simp at hordV₀
  have hpoles : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) < 0 → V.ord g < 0 := by
    intro V hV
    by_contra hge
    have hge : 0 ≤ V.ord g := le_of_not_gt hge
    have hgmem : g ∈ V.toValuationSubring := by
      rcases eq_or_ne g 0 with rfl | hg0
      · exact zero_mem _
      · exact SkitFixedAux.mem_of_ord_nonneg V hg0 hge
    have := SkitFixedAux.ord_nonneg_of_mem V (sub_mem hgmem (V.algebraMap_mem' (c : AlgebraicClosure ℚ)))
    omega

  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) :=
    (ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField (AlgebraicClosure ℚ) M H).1
  obtain ⟨q, hq, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) hgc0
  have hqpoles : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), q W < 0 → W = V₀ ∨ (Psp.reduceFst α hα W ∉ B ∧ Psp.reduceSnd β hβ δ W ∉ B) := by
    intro W hW
    by_cases hWV₀ : W = V₀
    · exact Or.inl hWV₀
    · exact Or.inr (hother W hWV₀ (hpoles W ((hq W) ▸ hW)))

  have hres₁' : (Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₁'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = (Rpd.R₁.residue ⟨g, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) - algebraMap (ResidueField ↥A) _ cb := by
    rw [hr₁]
  have hres₂' : (Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₂'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = (Rpd.R₂.residue ⟨g, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) - algebraMap (ResidueField ↥A) _ cb := by
    rw [hr₂]
  have hF₁' : ∀ w ∈ B, ¬ 0 < w.ord (Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₁'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := by
    intro w hw; rw [hres₁']; exact hF₁ w (Finset.mem_coe.mpr hw)
  have hF₂' : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p w ∈ B ∨ ∃ b ∈ B, w = δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p b)) → ¬ 0 < w.ord (Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₂'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) := by
    intro w hw; rw [hres₂']
    refine hF₂ w ?_
    rcases hw with hw | ⟨b, hb, rfl⟩
    · exact Or.inl (Set.mem_preimage.mpr (Finset.mem_coe.mpr hw))
    · exact Or.inr (Set.mem_image_of_mem _ (Finset.mem_coe.mpr hb))

  have hres' : Psp.reduceFst α hα V₀ ∈ B →
      ((Psp.reduceFst α hα V₀).ord (Rpd.R₁.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₁'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = -1 ∨
        (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα V₀))).ord (Rpd.R₂.residue ⟨g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ), h₂'⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) = -1) := by
    intro _
    rcases hres with ⟨e1, -⟩ | ⟨-, e2⟩
    · left; rw [hres₁', SkitFixedAux.ord_sub_algebraMap_of_neg _ (by rw [e1]; norm_num), e1]
    · right; rw [hres₂', SkitFixedAux.ord_sub_algebraMap_of_neg _ (by rw [e2]; norm_num), e2]

  have hnozero : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V ≠ V₀ → 0 < V.ord (g - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (c : AlgebraicClosure ℚ)) → Psp.reduceFst α hα V ∉ B := by
    intro V hVne hpos hB
    have hzero : 0 < q V := (hq V).symm ▸ hpos
    by_cases haffV : JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα V)
    · by_cases hfixV : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceFst α hα V)
      · exact SkitFixedAux.case_fixed p M H hpM A θ α β hα hβ δ Psp Rpd B V₀ _ h₁' h₂' hr₁ne hr₂ne q hq hqpoles hF₁' hF₂'
          V hVne hzero hO ((hq V₀).trans hordV₀) hres' hfixV haffV hB
      · rcases hTD V with hsnd | hfst
        · by_cases hfix2 : JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd β hβ δ V)
          · exact hfixV (hsnd ▸ (SkitFixedAux.fixed_frob_iff p M H hpM A δ hcomm _).mpr hfix2)
          · exact SkitFixedAux.case_strictSnd p M H hpM A θ α β hα hβ δ Psp Rpd B V₀ _ h₁' h₂' hr₁ne hr₂ne q hq hqpoles hF₁' hF₂'
              V hVne hzero hfix₂ hDLS ⟨hsnd, hfix2⟩ hB
        · exact SkitFixedAux.case_strictFst p M H hpM A θ α β hα hβ δ Psp Rpd B V₀ _ h₁' h₂' hr₁ne hr₂ne q hq hqpoles hF₁' hF₂'
            V hVne hzero hfix hDLF ⟨hfst, hfixV⟩ hB
    · have hcV := SkitFixedAux.isCuspidal_of_not_isAffinePlace p M H hpM hpM2 A hA α hα_coe hα Psp V haffV
      rcases ModularCurve.JHPlaceSpecialization.isInftySide_or_isZeroSide_of_isCuspidal p M H hpM A hA V hcV with hinf | hzer
      · exact SkitFixedAux.case_infty p M H hpM A θ α β hα hβ δ Psp Rpd B V₀ _ h₁' h₂' hr₁ne hr₂ne q hq hqpoles hF₁' hF₂'
          V hVne hzero hnc₀ hCLI hinf hB
      · exact SkitFixedAux.case_zero p M H hpM A θ α β hα hβ δ Psp Rpd B V₀ _ h₁' h₂' hr₁ne hr₂ne q hq hqpoles hF₁' hF₂'
          V hVne hzero hnc₀' hCLZ horient0 hzer hB
  exact ⟨c, h₁', h₂', hr₁ne, hr₂ne, hordV₀, hpoles, hnozero, q, fun V => hq V, hdeg⟩

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_sub_algebraMap_forall_ord_pos_reduceFst_notMem_of_fixed_of_isAffinePlace
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_exists_sub_algebraMap_forall_ord_pos_reduceFst_notMem_of_fixed_of_isAffinePlace (solution)
