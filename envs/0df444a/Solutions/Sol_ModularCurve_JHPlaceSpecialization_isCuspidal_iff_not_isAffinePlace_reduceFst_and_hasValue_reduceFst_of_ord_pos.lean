-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/af723a1d-d6fa-5e27-b316-590c4cd0637f

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_pos_sp_sub_algebraMap_of_ord_pos
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHPlaceSpecialization_isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "JHNeronObjectAtP.Fbar JHNeronObjectAtP coeffMap algebraMap_laurentSeries_eq_single coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange coeffMap_jqModC jqModC coeff_jqModC_neg_one infSubgroup xHFunctionField xHFunctionFieldBar qExpFunctionFieldC intFormRatiosC_subset JHPlaceSpecialization.IsAffinePlace JHPlaceSpecialization JHPlaceSpecialization.IsCuspidal JHPlaceSpecialization.ord_pos_sp_sub_algebraMap_of_ord_pos JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le jqModC_mem_intFormRatiosC JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar"
namespace JHPlaceSpecialization
p2m_export "ModularCurve.JHPlaceSpecialization" "IsAffinePlace reduceFst IsCuspidal ord_pos_sp_sub_algebraMap_of_ord_pos ord_sp_neg_of_forall_ord_sub_algebraMap_le"
namespace GoodReadKit
p2m_open "ModularCurve.JHPlaceSpecialization ModularCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ne_zero_of_ord_ne_zero (v : Place K F) {f : F} (h : v.ord f ≠ 0) : f ≠ 0 := by
  rintro rfl
  exact h (Place.ord_zero v)

theorem hasValue_of_ord_sub_pos (v : Place K F) (g : F) (b : K)
    (h : 0 < v.ord (g - algebraMap K F b)) : v.HasValue g b := by
  have hne : g - algebraMap K F b ≠ 0 := ne_zero_of_ord_ne_zero v h.ne'
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := v.mem_of_ord_nonneg hne h.le
  have hgmem : g ∈ v.toValuationSubring := by
    have := add_mem hmem (v.algebraMap_mem' b)
    simpa using this
  refine ⟨hgmem, ?_⟩

  have hnu : ¬ IsUnit (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord (g - algebraMap K F b) = 0 at h0
    omega
  have hmax : (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F b, hmem⟩ = 0 :=
    (IsLocalRing.residue_eq_zero_iff _).mpr hmax
  have hsplit : (⟨g, hgmem⟩ : v.toValuationSubring) =
      ⟨g - algebraMap K F b, hmem⟩ + algebraMap K v.toValuationSubring b := by
    ext
    simp
  rw [hsplit, map_add, hres0, zero_add, Place.residue_algebraMap]

theorem ord_sub_pos_of_hasValue (v : Place K F) {g : F} {b : K} (h : v.HasValue g b)
    (hne : g ≠ algebraMap K F b) : 0 < v.ord (g - algebraMap K F b) := by
  obtain ⟨hg, hres⟩ := h
  have hmem : g - algebraMap K F b ∈ v.toValuationSubring := sub_mem hg (v.algebraMap_mem' b)
  have hres0 : IsLocalRing.residue v.toValuationSubring ⟨g - algebraMap K F b, hmem⟩ = 0 := by
    have hsplit : (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) =
        ⟨g, hg⟩ - algebraMap K v.toValuationSubring b := by
      ext
      simp
    rw [hsplit, map_sub, hres, Place.residue_algebraMap, sub_self]
  have hmax : (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
    (IsLocalRing.residue_eq_zero_iff _).mp hres0
  have hnu : ¬ IsUnit (⟨g - algebraMap K F b, hmem⟩ : v.toValuationSubring) :=
    (IsLocalRing.mem_maximalIdeal _).mp hmax
  have hne' : g - algebraMap K F b ≠ 0 := sub_ne_zero.mpr hne
  have hnn : 0 ≤ v.ord (g - algebraMap K F b) := v.ord_nonneg_of_mem hmem
  rcases hnn.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨hm, hu⟩ := v.exists_isUnit_of_ord_eq_zero hne' heq.symm
    exact hnu hu

theorem not_mem_iff_ord_neg (v : Place K F) {f : F} (hf : f ≠ 0) :
    f ∉ v.toValuationSubring ↔ v.ord f < 0 := by
  constructor
  · intro h
    by_contra hge
    push Not at hge
    exact h (v.mem_of_ord_nonneg hf hge)
  · intro h hmem
    have := v.ord_nonneg_of_mem hmem
    omega

end ModularCurve.JHPlaceSpecialization.GoodReadKit

open ModularCurve.JHPlaceSpecialization.GoodReadKit

private noncomputable abbrev algebraQExpShortcut (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
    Algebra K ↥(qExpFunctionFieldC K Γ) := inferInstance

private noncomputable abbrev algebraBaseChangeShortcut (L : Type*) [Field L] [Algebra ℚ L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) : Algebra L ↥(laurentBaseChange L F₀) := inferInstance

attribute [local instance high] algebraQExpShortcut algebraBaseChangeShortcut

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Psp : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H))
    (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))
    (hxb : ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) :
    (JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V ↔
        ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V)) ∧
      (∀ a : ↥A, 0 < V.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ)) →
        (Psp.reduceFst α hα V).HasValue xb (IsLocalRing.residue ↥A a)) ∧
      (∀ b : ResidueField ↥A, (Psp.reduceFst α hα V).HasValue xb b →
        ∃ a : ↥A, IsLocalRing.residue ↥A a = b ∧
          0 < V.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))) := by
  classical

  have hx₀mem : jqModC (AlgebraicClosure ℚ) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := by
    have h1 : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) :=
      intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
    have h2 := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) h1
    have h3 : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := by
      show coeffMap _ _ = _
      exact coeffMap_jqModC _
    rw [h3] at h2
    exact h2
  set x₀ : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := ⟨jqModC (AlgebraicClosure ℚ), hx₀mem⟩ with hx₀def
  have hαx₀ : α x₀ = x := by
    apply Subtype.ext
    rw [hα_coe x₀, hx]

  have hαsub : ∀ a : ↥A, α (x₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) = x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ)) := by
    intro a
    rw [map_sub, hαx₀, AlgHom.commutes]

  have he_pos : 0 < Place.ramificationIndexAlong α V := by
    unfold Place.ramificationIndexAlong
    letI := algebraAlong α
    haveI := isIntegral_along α hα
    exact V.ramificationIndex_pos (F := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))

  have hord_iff : ∀ a : ↥A, 0 < V.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) ↔
      0 < (V.restrictAlong α hα).ord (x₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) := by
    intro a
    have h := Place.ord_restrictAlong α hα V (x₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ)))
    rw [hαsub] at h
    rw [h]
    constructor
    · intro hpos
      by_contra hle
      push Not at hle
      have : (Place.ramificationIndexAlong α V : ℤ) * (V.restrictAlong α hα).ord (x₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) hle
      omega
    · intro hpos
      exact mul_pos (Int.natCast_pos.mpr he_pos) hpos

  have hxuniq : ∀ x' : ↥(xHFunctionFieldBar M H), ((x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) → x' = x := by
    intro x' hx'
    exact Subtype.ext (hx'.trans hx.symm)
  have hxbuniq : ∀ x' : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), ((x' : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) → x' = xb := by
    intro x' hx'
    exact Subtype.ext (hx'.trans hxb.symm)

  have hxb_ne_const : ∀ b : ResidueField ↥A, (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ≠ algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) b := by
    intro b h
    have hc := congrArg (fun z : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) => ((z : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)).coeff (-1)) h
    rw [hxb, ModularCurve.coeff_jqModC_neg_one] at hc
    have : ((algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) b : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) = algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) b := rfl
    rw [this, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by norm_num)] at hc
    exact one_ne_zero hc
  have hxb0 : (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ≠ 0 := by
    intro h
    apply hxb_ne_const 0
    rw [h, map_zero]

  have hsurj : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), Function.Surjective (algebraMap (ResidueField ↥A) w.ResidueField) :=
    (ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
      p M H hpM hpM2 (ResidueField ↥A)).2.2

  have haff_iff : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      JHPlaceSpecialization.IsAffinePlace p M H hpM A w ↔ (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∈ w.toValuationSubring := by
    intro w
    constructor
    · rintro ⟨x', a', hx', hval⟩
      rw [hxbuniq x' hx'] at hval
      exact hval.mem
    · intro hmem
      obtain ⟨b, hb, -⟩ := w.exists_hasValue_of_surjective (hsurj w) hmem
      exact ⟨xb, b, hxb, hb⟩

  have h2 : ∀ a : ↥A, 0 < V.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : (AlgebraicClosure ℚ))) →
      (Psp.reduceFst α hα V).HasValue xb (IsLocalRing.residue ↥A a) := by
    intro a ha
    have hdown := (hord_iff a).mp ha
    have hz := ModularCurve.JHPlaceSpecialization.ord_pos_sp_sub_algebraMap_of_ord_pos p M H hpM hpM2 A hA Psp
      x₀ xb rfl hxb (V.restrictAlong α hα) a hdown
    exact hasValue_of_ord_sub_pos _ _ _ hz

  have h1a : JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V →
      ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) := by
    intro hcusp haff
    have hle : ∀ a : ↥A, (V.restrictAlong α hα).ord (x₀ - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : (AlgebraicClosure ℚ))) ≤ 0 := by
      intro a
      by_contra hlt
      push Not at hlt
      have hup := (hord_iff a).mpr hlt
      exact absurd hup (not_lt.mpr (hcusp x hx a))
    have hpole := ModularCurve.JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le p M H hpM hpM2 A hA Psp
      x₀ xb rfl hxb (V.restrictAlong α hα) hle
    have hnot : (xb : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) ∉ (Psp.reduceFst α hα V).toValuationSubring :=
      (not_mem_iff_ord_neg _ hxb0).mpr hpole
    exact hnot ((haff_iff _).mp haff)

  have h1b : ¬ JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) →
      JHPlaceSpecialization.IsCuspidal (M := M) (H := H) (A := A) V := by
    intro hnaff x' hx' a
    rw [hxuniq x' hx']
    by_contra hlt
    push Not at hlt
    exact hnaff ⟨xb, _, hxb, h2 a hlt⟩
  refine ⟨⟨h1a, h1b⟩, h2, ?_⟩

  intro b hb
  have haff : JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα V) := ⟨xb, b, hxb, hb⟩
  by_cases hex : ∃ a : ↥A, 0 < V.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (a : AlgebraicClosure ℚ))
  · obtain ⟨a, ha⟩ := hex
    exact ⟨a, Place.HasValue.unique (h2 a ha) hb, ha⟩
  · exfalso
    refine h1a ?_ haff
    intro x' hx' a
    rw [hxuniq x' hx']
    exact not_lt.mp (fun h => hex ⟨a, h⟩)

end S_ModularCurve_JHPlaceSpecialization_isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_isCuspidal_iff_not_isAffinePlace_reduceFst_and_hasValue_reduceFst_of_ord_pos (solution)
