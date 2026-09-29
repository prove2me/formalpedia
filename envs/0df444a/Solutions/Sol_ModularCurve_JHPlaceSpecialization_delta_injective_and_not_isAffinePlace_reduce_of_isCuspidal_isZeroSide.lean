-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/50fffb06-2fdd-5c65-bfdd-e0de27cd900c

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
import Theorems.Thm_AlgebraicCurve_Place_one_le_ramificationIndexAlong
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_Place_deg_eq_one_iff_surjective_algebraMap_residueField
import Theorems.Thm_AlgebraicCurve_Place_ord_add_eq_of_lt
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆"
p2m_attr_erase "simp" "ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JHPlaceSpecialization_delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide.AlgebraicCurve IsLocalRing ModularCurve"
open scoped MatrixGroups

set_option autoImplicit false

namespace Readings3

theorem ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  by_cases hf0 : f = 0
  · rw [hf0, Place.ord_zero]
  by_contra hneg
  push Not at hneg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf0 hπ

  have hπ0 : ((π : v.toValuationSubring) : F) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hzmem : ((π : v.toValuationSubring) : F) ^ (v.ord f) ∈ v.toValuationSubring := by
    have hinv : ((((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring)) : F) *
        (((u : v.toValuationSubringˣ) : v.toValuationSubring) : F) = 1 := by
      rw [← MulMemClass.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, OneMemClass.coe_one]
    have : ((π : v.toValuationSubring) : F) ^ (v.ord f) =
        ((((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring)) : F) * f := by
      conv_rhs => rw [hu]
      rw [← mul_assoc, hinv, one_mul]
    rw [this]
    exact mul_mem (SetLike.coe_mem _) hf

  set n : ℤ := v.ord f with hn
  have hprod : ((π : v.toValuationSubring) : F) ^ n * ((π : v.toValuationSubring) : F) ^ (-n) = 1 := by
    rw [← zpow_add₀ hπ0, add_neg_cancel, zpow_zero]
  have hnat : ((π : v.toValuationSubring) : F) ^ (-n) = (((π ^ (-n).toNat : v.toValuationSubring)) : F) := by
    rw [SubmonoidClass.coe_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  have hunit : IsUnit (π ^ (-n).toNat : v.toValuationSubring) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hzmem⟩, Subtype.ext ?_⟩
    show (((π ^ (-n).toNat : v.toValuationSubring)) : F) * ((π : v.toValuationSubring) : F) ^ n = 1
    rw [← hnat, mul_comm, hprod]
  have hk : 1 ≤ (-n).toNat := by omega
  obtain ⟨k, hk'⟩ := Nat.exists_eq_add_of_le hk
  rw [hk', pow_add, pow_one] at hunit
  exact hπ.not_isUnit (isUnit_of_mul_isUnit_left hunit)

theorem not_isAffinePlace_reduceFst_of_isCuspidal
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A)
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hC : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C) :
    ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα C) := by
  rintro ⟨xb, a, hxb, hval⟩

  have hαx : ((α x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hα_coe, hx]
  have hdown : ∀ b : ↥A, (C.restrictAlong α hα).ord (x - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) ≤ 0 := by
    intro b
    have h1 := hC (α x) hαx b
    have h2 : α x - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ) = α (x - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) := by
      rw [map_sub, AlgHom.commutes]
    rw [h2, Place.ord_restrictAlong α hα] at h1
    have he := Place.one_le_ramificationIndexAlong α hα C
    by_contra hpos
    push Not at hpos
    have : (1 : ℤ) ≤ (Place.ramificationIndexAlong α C : ℤ) * (C.restrictAlong α hα).ord (x - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) :=
      one_le_mul_of_one_le_of_one_le (by exact_mod_cast he) hpos
    omega

  have hpole := JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le p M H hpM hpM2 A hA Psp x xb hx hxb
    (C.restrictAlong α hα) hdown
  have heq : Psp.sp (C.restrictAlong α hα) = Psp.reduceFst α hα C := rfl
  rw [heq] at hpole

  have hnn := ord_nonneg_of_mem (Psp.reduceFst α hα C) hval.mem
  omega

end Readings3

namespace Readings3

theorem not_isAffinePlace_of_ord_neg
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hv : v.ord xb < 0) :
    ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) v := by
  rintro ⟨xb', a, hxb', hval⟩
  have hx : xb' = xb := Subtype.ext (by rw [hxb', hxb])
  rw [hx] at hval
  have := ord_nonneg_of_mem v hval.mem
  omega

theorem ofAlgAut_inv_smul_smul {K F : Type*} [Field K] [Field F] [Algebra K F] {G : Type*} [Group G]
    (ρ : G →* (F ≃ₐ[K] F)) (g : G) (w : Place K F) :
    SemilinearAut.ofAlgAut (ρ g⁻¹) • (SemilinearAut.ofAlgAut (ρ g) • w) = w := by
  rw [← mul_smul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, one_smul]

set_option maxHeartbeats 1600000 in

theorem not_isAffinePlace_reduceSnd_of_isCuspidal'
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hβ : β.IsIntegral)
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hC : JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) C) :
    ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceSnd β hβ δ C) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hβx : ((β x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := by
    rw [hβ_coe, hx]
  have hdown : ∀ b : ↥A, (C.restrictAlong β hβ).ord (x - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) ≤ 0 := by
    intro b
    have h1 := hC (β x) hβx b
    have h2 : β x - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ) = β (x - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) := by
      rw [map_sub, AlgHom.commutes]
    rw [h2, Place.ord_restrictAlong β hβ] at h1
    have he := Place.one_le_ramificationIndexAlong β hβ C
    by_contra hpos
    push Not at hpos
    have : (1 : ℤ) ≤ (Place.ramificationIndexAlong β C : ℤ) * (C.restrictAlong β hβ).ord (x - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) :=
      one_le_mul_of_one_le_of_one_le (by exact_mod_cast he) hpos
    omega
  have hpole := JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le p M H hpM hpM2 A hA Psp x xb hx hxb
    (C.restrictAlong β hβ) hdown

  intro haff
  have heq : Psp.reduceSnd β hβ δ C = δ (Psp.sp (C.restrictAlong β hβ)) := rfl
  rw [heq, hδ] at haff
  have hback := (JHPlaceSpecialization.isAffinePlace_qExpFrobeniusPlaceModL_and_isAffinePlace_smul_diamondActionModL
    p M H hpM A hA).2 (CuspForm.gammaLift (M / p) pb)⁻¹ _ haff
  rw [ofAlgAut_inv_smul_smul (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM))
    (CuspForm.gammaLift (M / p) pb) (Psp.sp (C.restrictAlong β hβ))] at hback
  exact not_isAffinePlace_of_ord_neg p M H hpM A xb hxb _ hpole hback

end Readings3

namespace Readings3

end Readings3

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place.ramificationIndexAlong Place.ord_restrictAlong Place Place.ord_zero SemilinearAut SemilinearAut.ofAlgAut Place.HasValue Place.hasValue_one Place.hasValue_algebraMap Place.exists_hasValue_of_surjective Place.one_le_ramificationIndexAlong Place.deg_eq_one_iff_surjective_algebraMap_residueField Place.ord_add_eq_of_lt"
namespace Place
p2m_export "AlgebraicCurve.Place" "restrictAlong ramificationIndexAlong ord_restrictAlong ext ResidueField deg ord ord_zero ord_mul ord_zpow exists_unit_mul_zpow toValuationSubring HasValue hasValue_one hasValue_algebraMap exists_isUnit_of_ord_eq_zero exists_hasValue_of_surjective ord_nonneg_of_mem one_le_ramificationIndexAlong deg_eq_one_iff_surjective_algebraMap_residueField ord_add_eq_of_lt"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem mem_of_ord_nonneg' {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm, zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

variable {v}

namespace HasValue p2m_export "AlgebraicCurve.Place.HasValue" "mem residue_eq mul ne_zero ord_eq_zero" end HasValue
p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.sub' {g g' : F} {a a' : K} (h : v.HasValue g a) (h' : v.HasValue g' a') :
    v.HasValue (g - g') (a - a') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨sub_mem hg hg', ?_⟩
  have hx : (⟨g - g', sub_mem hg hg'⟩ : v.toValuationSubring) = ⟨g, hg⟩ - ⟨g', hg'⟩ := rfl
  rw [hx, map_sub, hr, hr', map_sub]

p2m_open_scoped "AlgebraicCurve.Place.HasValue" in
theorem HasValue.pow' {g : F} {a : K} (h : v.HasValue g a) (n : ℕ) : v.HasValue (g ^ n) (a ^ n) := by
  induction n with
  | zero => simpa using Place.hasValue_one v
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

p2m_open_scoped "AlgebraicCurve.Place.HasValue" in

theorem HasValue.ord_pos_of_zero {g : F} (h : v.HasValue g 0) (hg : g ≠ 0) : 0 < v.ord g := by
  have hnn := Readings3.ord_nonneg_of_mem v h.mem
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hg heq.symm
    have hres := h.residue_eq
    rw [map_zero] at hres
    have h' : IsLocalRing.residue _ (⟨g, hm⟩ : v.toValuationSubring) ≠ 0 := by
      rw [IsLocalRing.residue_ne_zero_iff_isUnit]; exact hu
    exact h' hres

end AlgebraicCurve.Place

namespace Readings3

set_option maxHeartbeats 1600000 in
theorem isCuspidal_of_isZeroSide
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hZ : JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C) :
    JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨hC', x, x', hx, hx', τ, hτ, hval⟩ := hZ
  intro y hy a
  have hyx : y = x := Subtype.ext (by rw [hy, hx])
  rw [hyx]

  have hτ0 : ((τ : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    have : τ = 0 := Subtype.ext h0
    rw [this, map_zero] at hτ
    exact zero_ne_one hτ
  have hu0 : x / x' ^ p ≠ 0 := hval.ne_zero hτ0
  have hx'p0 : x' ^ p ≠ 0 := by
    intro h0; apply hu0; rw [h0, div_zero]
  have hx'0 : x' ≠ 0 := fun h0 => hx'p0 (by rw [h0, zero_pow (NeZero.ne p)])
  have hx0 : x ≠ 0 := by
    intro h0; apply hu0; rw [h0, zero_div]
  have hordu : C.ord (x / x' ^ p) = 0 := hval.ord_eq_zero hτ0
  have hxeq : x = x / x' ^ p * x' ^ p := (div_mul_cancel₀ x hx'p0).symm
  have hordx : C.ord x = (p : ℤ) * C.ord x' := by
    conv_lhs => rw [hxeq]
    rw [C.ord_mul hu0 hx'p0, hordu, zero_add, ← zpow_natCast, C.ord_zpow]

  have hconst : ∀ c : AlgebraicClosure ℚ, c ≠ 0 → C.ord (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c) = 0 :=
    fun c hc => (Place.hasValue_algebraMap C c).ord_eq_zero hc
  by_cases hneg : C.ord x' < 0
  ·
    have hxneg : C.ord x < 0 := by
      rw [hordx]
      have hp : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      nlinarith
    by_cases ha : ((a : ↥A) : AlgebraicClosure ℚ) = 0
    · rw [ha, map_zero, sub_zero]; exact hxneg.le
    · have hca : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (-(a : AlgebraicClosure ℚ)) ≠ 0 := by
        rw [map_ne_zero_iff _ (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).injective]
        exact neg_ne_zero.mpr ha
      have h1 : x - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) = x + algebraMap (AlgebraicClosure ℚ) _ (-(a : AlgebraicClosure ℚ)) := by
        rw [map_neg, sub_eq_add_neg]
      rw [h1, Place.ord_add_eq_of_lt C hx0 hca (by rw [hconst _ (neg_ne_zero.mpr ha)]; exact hxneg)]
      exact hxneg.le
  ·
    push Not at hneg
    have hmem' : x' ∈ C.toValuationSubring := Place.mem_of_ord_nonneg' C hx'0 hneg

    haveI : (CohCarrier.GammaH M H).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
    have hdeg : C.deg = 1 := place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC (AlgebraicClosure ℚ) (CohCarrier.GammaH M H)
      (translation_mem_GammaH M H) (xHFunctionField M H) rfl C
    have hsurj := (Place.deg_eq_one_iff_surjective_algebraMap_residueField C).mp hdeg
    obtain ⟨c, hc, -⟩ := Place.exists_hasValue_of_surjective C hsurj hmem'
    by_cases hcA : ∃ b : ↥A, (b : AlgebraicClosure ℚ) = c
    ·
      exfalso
      obtain ⟨b, hb⟩ := hcA
      have hval0 : C.HasValue (x' - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ)) 0 := by
        rw [hb]
        have := Place.HasValue.sub' hc (Place.hasValue_algebraMap C c)
        rwa [sub_self] at this
      have hne : x' - algebraMap (AlgebraicClosure ℚ) _ (b : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0
        have h1 : ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
            ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
          rw [sub_eq_zero.mp h0]
        have h2 : ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
            = HahnSeries.single 0 ((b : AlgebraicClosure ℚ)) := by
          rw [show ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (b : AlgebraicClosure ℚ) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ))
              = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (b : AlgebraicClosure ℚ) from rfl]
          exact algebraMap_laurentSeries_eq_single _ _
        rw [hx', h2] at h1
        have h3 := congrArg (fun s : LaurentSeries (AlgebraicClosure ℚ) => s.coeff ((p : ℤ) * (-1))) h1
        simp only [qExpand_coeff_mul, coeff_jqModC_neg_one] at h3
        rw [HahnSeries.coeff_single_of_ne] at h3
        · exact one_ne_zero h3
        · have : (p : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne p)
          omega
      have hpos := Place.HasValue.ord_pos_of_zero hval0 hne
      have hle := hC' x' hx' b
      omega
    ·
      push Not at hcA
      have hvalx : C.HasValue x ((τ : AlgebraicClosure ℚ) * c ^ p) := by
        have := hval.mul (Place.HasValue.pow' hc p)
        rwa [div_mul_cancel₀ x hx'p0] at this
      have hd : (τ : AlgebraicClosure ℚ) * c ^ p - (a : AlgebraicClosure ℚ) ≠ 0 := by
        intro h0

        have hτu : IsUnit τ := by
          rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hτ]; exact one_ne_zero
        obtain ⟨w, hw⟩ := hτu
        have h1 : ((τ : ↥A) : AlgebraicClosure ℚ) * c ^ p = (a : AlgebraicClosure ℚ) := sub_eq_zero.mp h0
        have h2 : (((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * ((τ : ↥A) : AlgebraicClosure ℚ) = 1 := by
          rw [← hw, ← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl
        have hcp : c ^ p = (((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * (a : AlgebraicClosure ℚ) := by
          calc c ^ p = ((((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * ((τ : ↥A) : AlgebraicClosure ℚ)) * c ^ p := by
                rw [h2, one_mul]
            _ = (((w⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) * (((τ : ↥A) : AlgebraicClosure ℚ) * c ^ p) := by ring
            _ = _ := by rw [h1]
        have hcpA : c ^ p ∈ A := by
          rw [hcp]; exact mul_mem (SetLike.coe_mem _) (SetLike.coe_mem _)
        have hint : IsIntegral ↥A (c ^ p) := by
          have : c ^ p = algebraMap ↥A (AlgebraicClosure ℚ) ⟨c ^ p, hcpA⟩ := rfl
          rw [this]; exact isIntegral_algebraMap
        have hint' : IsIntegral ↥A c := IsIntegral.of_pow (Fact.out : p.Prime).pos hint
        obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint'
        exact hcA b hb
      have := (Place.HasValue.sub' hvalx (Place.hasValue_algebraMap C (a : AlgebraicClosure ℚ))).ord_eq_zero hd
      rw [this]

end Readings3

open Readings3 in
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
    (Psp : JHPlaceSpecialization p M H hpM A)
    (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hFix : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)
    (hmodel : Rpd.IsModel α β hα hβ δ)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w)) :
    Function.Injective δ ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) C → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα C)) ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsCuspidal' (p := p) (M := M) (H := H) (A := A) C → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceSnd β hβ δ C)) ∧
    (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C → ¬ JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A) (Psp.reduceFst α hα C)) := by
  classical

  have hjℚ : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) :=
    x0_le_xHFunctionFieldC (K := ℚ) (M := M / p) (H := infSubgroup p M H hpM)
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 ℚ (M / p) (jqModC_mem_full (K := ℚ) (N := M / p)))
  let x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) hjℚ⟩
  have hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    show coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ)
    exact coeffMap_jqModC _
  have hjκ : jqModC (ResidueField ↥A) ∈ qExpFunctionFieldC (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) :=
    x0_le_xHFunctionFieldC (K := ResidueField ↥A) (M := M / p) (H := infSubgroup p M H hpM)
      (ModularCurve.modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 (ResidueField ↥A) (M / p)
        (jqModC_mem_full (K := ResidueField ↥A) (N := M / p)))
  let xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) := ⟨jqModC (ResidueField ↥A), hjκ⟩
  have hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    intro v w h
    rw [hδ, hδ] at h
    have := congrArg (fun u => SemilinearAut.ofAlgAut
      (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)⁻¹) • u) h
    simpa only [ofAlgAut_inv_smul_smul] using this
  · intro C hC
    exact not_isAffinePlace_reduceFst_of_isCuspidal p M H hpM hpM2 A hA α hα hα_coe Psp x hx C hC
  · intro C hC
    exact not_isAffinePlace_reduceSnd_of_isCuspidal' p M H hpM hpM2 A hA β hβ hβ_coe pb δ hδ Psp x hx xb hxb C hC
  · intro C hC
    exact not_isAffinePlace_reduceFst_of_isCuspidal p M H hpM hpM2 A hA α hα hα_coe Psp x hx C
      (isCuspidal_of_isZeroSide p M H A C hC)

end S_ModularCurve_JHPlaceSpecialization_delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_delta_injective_and_not_isAffinePlace_reduce_of_isCuspidal_isZeroSide (solution)
