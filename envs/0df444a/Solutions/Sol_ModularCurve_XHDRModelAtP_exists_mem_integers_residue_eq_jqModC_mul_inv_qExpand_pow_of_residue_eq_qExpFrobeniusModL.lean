-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ab7ed1cb-829b-5ebc-b70e-a152d1657d28

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_ModularCurve_XHOperators
import Theorems.Thm_ModularCurve_XHDRModelAtP_integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_integers_comap_eq_integers_comap_of_residue_eq_qExpFrobeniusModL
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss
import Theorems.Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Theorems.Thm_ModularCurve_GammaH_le_GammaH_div_infSubgroup
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve~laurentBaseChange_mono ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

namespace Res2T

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd N _ hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem qExpand_ne_zero {K : Type} [Field K] (N : ℕ) [NeZero N] {s : LaurentSeries K} (hs : s ≠ 0) : qExpand K N s ≠ 0 :=
  fun h => hs (qExpand_injective N (h.trans (map_zero _).symm))

theorem residue_eq_zero_iff {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb) (f : F) (h : f ∈ R.integers) :
    R.residue ⟨f, h⟩ = 0 ↔ R.integers.valuation f < 1 := by
  rw [← RingHom.mem_ker, R.ker_residue]
  exact R.integers.valuation_lt_one_iff ⟨f, h⟩

theorem inv_mem_of_residue_ne_zero {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb) (f : F) (h : f ∈ R.integers) (hr : R.residue ⟨f, h⟩ ≠ 0) :
    f⁻¹ ∈ R.integers := by
  have hlt : ¬ R.integers.valuation f < 1 := fun hh => hr ((residue_eq_zero_iff R f h).mpr hh)
  have hle : R.integers.valuation f ≤ 1 := (R.integers.valuation_le_one_iff f).mpr h
  have h1 : R.integers.valuation f = 1 := le_antisymm hle (not_lt.mp hlt)
  exact (R.integers.valuation_le_one_iff _).mp (by rw [map_inv₀, h1, inv_one])

theorem valuation_lt_one_iff_inv_not_mem {F : Type*} [Field F] (O : ValuationSubring F) {f : F} (hf : f ≠ 0) :
    O.valuation f < 1 ↔ f⁻¹ ∉ O := by
  rw [← O.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ ((Valuation.pos_iff _).mpr hf)]

theorem aeval_mem {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fb : Type*} [Field Fb] [Algebra (IsLocalRing.ResidueField A) Fb]
    (R : RegularProlongation A F Fb) (x : F) (hx : x ∈ R.integers) (Q : Polynomial ↥A) :
    Polynomial.aeval x (Q.map A.subtype) ∈ R.integers := by
  induction Q using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [Polynomial.map_add, map_add]
    exact add_mem hP hQ
  | monomial n a =>
    rw [Polynomial.map_monomial, Polynomial.aeval_monomial]
    exact mul_mem ((R.algebraMap_mem_iff (a : L)).mpr a.2) (pow_mem hx n)

theorem coeffMap_subtype_injective (A : ValuationSubring (AlgebraicClosure ℚ)) : Function.Injective (coeffMap A.subtype) := by
  intro a b hab
  apply HahnSeries.ext
  funext k
  apply Subtype.val_injective
  have := congrArg (fun z : LaurentSeries (AlgebraicClosure ℚ) => z.coeff k) hab
  simp only [coeffMap_coeff] at this
  exact this

theorem coeffMap_residue_cross (A : ValuationSubring (AlgebraicClosure ℚ)) (x y x₁ y₁ : LaurentSeries ↥A)
    (h : coeffMap A.subtype x * coeffMap A.subtype y₁ = coeffMap A.subtype x₁ * coeffMap A.subtype y) :
    coeffMap (IsLocalRing.residue ↥A) x * coeffMap (IsLocalRing.residue ↥A) y₁ =
      coeffMap (IsLocalRing.residue ↥A) x₁ * coeffMap (IsLocalRing.residue ↥A) y := by
  have h' : x * y₁ = x₁ * y := coeffMap_subtype_injective A (by rw [map_mul, map_mul]; exact h)
  rw [← map_mul, ← map_mul, h']

theorem laurentBaseChange_mono (L : Type*) [Field L] [Algebra ℚ L] {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)

theorem residue₁_mul_coeffMap_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers) (x y : LaurentSeries ↥A)
    (hxF : coeffMap A.subtype x ∈ xHFunctionFieldBar M H) (hyF : coeffMap A.subtype y ∈ xHFunctionFieldBar M H)
    (hxy : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ((Rpd.R₁.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) *
        coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x := by
  obtain ⟨hyR, hyres⟩ := Rpd.residue₁_coeffMap y hyF
  obtain ⟨hxR, hxres⟩ := Rpd.residue₁_coeffMap x hxF
  have hmul : (⟨f, hf⟩ : ↥Rpd.R₁.integers) * ⟨⟨coeffMap A.subtype y, hyF⟩, hyR⟩ =
      ⟨⟨coeffMap A.subtype x, hxF⟩, hxR⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    show ((f * ⟨coeffMap A.subtype y, hyF⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype x
    rw [MulMemClass.coe_mul]
    exact hxy
  have hres := congrArg (fun z : ↥Rpd.R₁.integers =>
    ((Rpd.R₁.residue z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A))) hmul
  simp only [map_mul, MulMemClass.coe_mul] at hres
  rw [hyres, hxres] at hres
  exact hres

theorem coe_apply_eq_qExpand_of_mem
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)] [NeZero p]
    (σb : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hle : xHFunctionField (M / p) (infSubgroup p M H hpM) ≤ xHFunctionField M H)
    (hgen : ∀ (u : LaurentSeries ℚ) (hu : u ∈ xHFunctionField (M / p) (infSubgroup p M H hpM)),
      ((σb ⟨coeffEmb (AlgebraicClosure ℚ) u, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hle hu)⟩ : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) u))
    (z : LaurentSeries (AlgebraicClosure ℚ)) (hz : z ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (hz' : z ∈ xHFunctionFieldBar M H) :
    ((σb ⟨z, hz'⟩ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p z := by
  have hmono : xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) ≤ xHFunctionFieldBar M H :=
    laurentBaseChange_mono (AlgebraicClosure ℚ) hle
  revert hz'
  rw [xHFunctionFieldBar, mem_laurentBaseChange_iff] at hz
  induction hz using Subfield.closure_induction with
  | mem y hy =>
      intro hz'
      rcases hy with ⟨a, rfl⟩ | ⟨u, hu, rfl⟩
      · have : (⟨algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a, hz'⟩ : ↥(xHFunctionFieldBar M H)) =
            algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) a := Subtype.ext rfl
        rw [this, AlgEquiv.commutes]
        show algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a = _
        rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
      · exact hgen u hu
  | one => intro hz'; rw [show (⟨(1 : LaurentSeries (AlgebraicClosure ℚ)), hz'⟩ : ↥(xHFunctionFieldBar M H)) = 1 from Subtype.ext rfl, map_one, map_one]; rfl
  | add x y hx hy ihx ihy =>
      intro hz'
      have hx' : x ∈ xHFunctionFieldBar M H := hmono hx
      have hy' : y ∈ xHFunctionFieldBar M H := hmono hy
      rw [show (⟨x + y, hz'⟩ : ↥(xHFunctionFieldBar M H)) = ⟨x, hx'⟩ + ⟨y, hy'⟩ from Subtype.ext rfl, map_add, map_add,
        AddMemClass.coe_add, ihx hx', ihy hy']
  | neg x hx ihx =>
      intro hz'
      have hx' : x ∈ xHFunctionFieldBar M H := hmono hx
      rw [show (⟨-x, hz'⟩ : ↥(xHFunctionFieldBar M H)) = -⟨x, hx'⟩ from Subtype.ext rfl, map_neg, map_neg, NegMemClass.coe_neg, ihx hx']
  | inv x hx ihx =>
      intro hz'
      have hx' : x ∈ xHFunctionFieldBar M H := hmono hx
      rw [show (⟨x⁻¹, hz'⟩ : ↥(xHFunctionFieldBar M H)) = (⟨x, hx'⟩)⁻¹ from Subtype.ext rfl, map_inv₀, map_inv₀, ← ihx hx']
      push_cast
      rfl
  | mul x y hx hy ihx ihy =>
      intro hz'
      have hx' : x ∈ xHFunctionFieldBar M H := hmono hx
      have hy' : y ∈ xHFunctionFieldBar M H := hmono hy
      rw [show (⟨x * y, hz'⟩ : ↥(xHFunctionFieldBar M H)) = ⟨x, hx'⟩ * ⟨y, hy'⟩ from Subtype.ext rfl, map_mul, map_mul,
        MulMemClass.coe_mul, ihx hx', ihy hy']

theorem heart
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (σb : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hσα : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((σb (α u) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (x y : LaurentSeries ↥A)
    (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (hxy : ((u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
      coeffMap A.subtype x) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ x' y' : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y' ≠ 0 ∧
      ((σb (α u) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y' = coeffMap A.subtype x' ∧
      coeffMap (IsLocalRing.residue ↥A) x' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) =
        qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) x) * coeffMap (IsLocalRing.residue ↥A) y' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine ⟨qExpand (↥A) p x, qExpand (↥A) p y, ?_, ?_, ?_⟩
  · rw [coeffMap_qExpand]
    exact fun h => hy (qExpand_injective p (h.trans (map_zero _).symm))
  · rw [hσα u, coeffMap_qExpand, coeffMap_qExpand, ← map_mul, hxy]
  · rw [coeffMap_qExpand, coeffMap_qExpand, mul_comm]

theorem key₁
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (σb : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hσα : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((σb (α u) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ hσ : σb (α v) ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨σb (α v), hσ⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
        qExpand (ResidueField ↥A) p ((Rpd.R₁.residue ⟨α v, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨x, y, hy, hxy⟩ := (ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss p M H hpM hpM2 hHp A hA θ Psp Rpd (α v)).mp h₁
  have hxyv : ((v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y =
      coeffMap A.subtype x := by rw [← hα_coe]; exact hxy
  obtain ⟨x', y', hy', hxy', hfrob⟩ := heart p M H hpM A α σb hσα v x y hy hxyv
  obtain ⟨x₁, y₁, hx₁F, hy₁F, hy₁, hxy₁⟩ :=
    ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA (α v) x y hy hxy
  obtain ⟨x₂, y₂, hx₂F, hy₂F, hy₂, hxy₂⟩ :=
    ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA (σb (α v)) x' y' hy' hxy'
  have hσ1 : σb (α v) ∈ Rpd.R₁.integers :=
    (ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss p M H hpM hpM2 hHp A hA θ Psp Rpd (σb (α v))).mpr
      ⟨x', y', hy', hxy'⟩
  refine ⟨hσ1, ?_⟩
  have e₁ := residue₁_mul_coeffMap_eq p M H hpM A θ Psp Rpd (α v) h₁ x₁ y₁ hx₁F hy₁F hxy₁
  have e₂ := residue₁_mul_coeffMap_eq p M H hpM A θ Psp Rpd (σb (α v)) hσ1 x₂ y₂ hx₂F hy₂F hxy₂
  have c₁ : coeffMap (IsLocalRing.residue ↥A) x * coeffMap (IsLocalRing.residue ↥A) y₁ =
      coeffMap (IsLocalRing.residue ↥A) x₁ * coeffMap (IsLocalRing.residue ↥A) y := by
    apply coeffMap_residue_cross
    rw [← hxy, ← hxy₁]; ring
  have c₂ : coeffMap (IsLocalRing.residue ↥A) x' * coeffMap (IsLocalRing.residue ↥A) y₂ =
      coeffMap (IsLocalRing.residue ↥A) x₂ * coeffMap (IsLocalRing.residue ↥A) y' := by
    apply coeffMap_residue_cross
    rw [← hxy', ← hxy₂]; ring
  set r₁ := ((Rpd.R₁.residue ⟨α v, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) with hr₁
  set r₂ := ((Rpd.R₁.residue ⟨σb (α v), hσ1⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) with hr₂
  have f₁ : r₁ * coeffMap (IsLocalRing.residue ↥A) y = coeffMap (IsLocalRing.residue ↥A) x := by
    apply mul_right_cancel₀ hy₁
    calc r₁ * coeffMap (IsLocalRing.residue ↥A) y * coeffMap (IsLocalRing.residue ↥A) y₁
        = (r₁ * coeffMap (IsLocalRing.residue ↥A) y₁) * coeffMap (IsLocalRing.residue ↥A) y := by ring
      _ = coeffMap (IsLocalRing.residue ↥A) x₁ * coeffMap (IsLocalRing.residue ↥A) y := by rw [e₁]
      _ = coeffMap (IsLocalRing.residue ↥A) x * coeffMap (IsLocalRing.residue ↥A) y₁ := c₁.symm
  have f₂ : r₂ * coeffMap (IsLocalRing.residue ↥A) y' = coeffMap (IsLocalRing.residue ↥A) x' := by
    apply mul_right_cancel₀ hy₂
    calc r₂ * coeffMap (IsLocalRing.residue ↥A) y' * coeffMap (IsLocalRing.residue ↥A) y₂
        = (r₂ * coeffMap (IsLocalRing.residue ↥A) y₂) * coeffMap (IsLocalRing.residue ↥A) y' := by ring
      _ = coeffMap (IsLocalRing.residue ↥A) x₂ * coeffMap (IsLocalRing.residue ↥A) y' := by rw [e₂]
      _ = coeffMap (IsLocalRing.residue ↥A) x' * coeffMap (IsLocalRing.residue ↥A) y₂ := c₂.symm
  have hne : coeffMap (IsLocalRing.residue ↥A) y' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) ≠ 0 :=
    mul_ne_zero hy' (qExpand_ne_zero p hy)
  apply mul_right_cancel₀ hne
  calc r₂ * (coeffMap (IsLocalRing.residue ↥A) y' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y))
      = (r₂ * coeffMap (IsLocalRing.residue ↥A) y') * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) := by ring
    _ = coeffMap (IsLocalRing.residue ↥A) x' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y) := by rw [f₂]
    _ = qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) x) * coeffMap (IsLocalRing.residue ↥A) y' := hfrob
    _ = qExpand (ResidueField ↥A) p (r₁ * coeffMap (IsLocalRing.residue ↥A) y) * coeffMap (IsLocalRing.residue ↥A) y' := by rw [f₁]
    _ = qExpand (ResidueField ↥A) p r₁ * (coeffMap (IsLocalRing.residue ↥A) y' * qExpand (ResidueField ↥A) p (coeffMap (IsLocalRing.residue ↥A) y)) := by rw [map_mul]; ring

theorem mem₁_and_residue_of_coe_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (f : ↥(xHFunctionFieldBar M H)) (y : LaurentSeries ↥A)
    (hf : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype y) :
    ∃ h : f ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨f, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = coeffMap (IsLocalRing.residue ↥A) y := by
  have hyF : coeffMap A.subtype y ∈ xHFunctionFieldBar M H := hf ▸ f.2
  obtain ⟨h, hres⟩ := Rpd.residue₁_coeffMap y hyF
  have hf' : f = ⟨coeffMap A.subtype y, hyF⟩ := Subtype.ext hf
  subst hf'
  exact ⟨h, hres⟩

theorem aeval_mem_and_inv_mem_of_residue_eq_qExpand
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (R : RegularProlongation A ↥(xHFunctionFieldBar M H) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ R.integers)
    (hres : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((R.residue ⟨f, hf⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
        qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)))
    (Q : Polynomial ↥A) (hQ : Q.map (IsLocalRing.residue ↥A) ≠ 0) :
    Polynomial.aeval f (Q.map A.subtype) ∈ R.integers ∧ (Polynomial.aeval f (Q.map A.subtype))⁻¹ ∈ R.integers := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hmem : Polynomial.aeval f (Q.map A.subtype) ∈ R.integers := aeval_mem R f hf Q
  refine ⟨hmem, inv_mem_of_residue_ne_zero R _ hmem ?_⟩
  set O := R.integers with hO
  let ι : ↥A →+* ↥O := ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).comp A.subtype).codRestrict O
    (fun a => (R.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)
  have hev : (⟨Polynomial.aeval f (Q.map A.subtype), hmem⟩ : ↥O) = Polynomial.eval₂ ι ⟨f, hf⟩ Q := by
    apply Subtype.ext
    show Polynomial.aeval f (Q.map A.subtype) = O.subtype (Polynomial.eval₂ ι ⟨f, hf⟩ Q)
    rw [Polynomial.hom_eval₂, Polynomial.aeval_def, Polynomial.eval₂_map]
    rfl
  have hresQ : R.residue ⟨Polynomial.aeval f (Q.map A.subtype), hmem⟩ =
      Polynomial.eval₂ (R.residue.comp ι) (R.residue ⟨f, hf⟩) Q := by
    rw [hev, Polynomial.hom_eval₂]
  have hι : R.residue.comp ι = (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).comp
      (IsLocalRing.residue ↥A) := by
    refine RingHom.ext fun a => ?_
    rw [RingHom.comp_apply]
    exact R.residue_algebraMap a
  have hcoe : ((R.residue ⟨Polynomial.aeval f (Q.map A.subtype), hmem⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) :
        LaurentSeries (ResidueField ↥A)) =
      qExpand (ResidueField ↥A) p (Polynomial.eval₂ (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)))
        (jqModC (ResidueField ↥A)) (Q.map (IsLocalRing.residue ↥A))) := by
    rw [hresQ, hι]
    show algebraMap (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (LaurentSeries (ResidueField ↥A))
      (Polynomial.eval₂ ((algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).comp
        (IsLocalRing.residue ↥A)) (R.residue ⟨f, hf⟩) Q) = _
    rw [Polynomial.hom_eval₂ Q _ (algebraMap (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (LaurentSeries (ResidueField ↥A)))
      (R.residue ⟨f, hf⟩), Polynomial.eval₂_map,
      Polynomial.hom_eval₂ Q _ (qExpand (ResidueField ↥A) p) (jqModC (ResidueField ↥A))]
    have hX : algebraMap (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (LaurentSeries (ResidueField ↥A))
        (R.residue ⟨f, hf⟩) = qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)) := hres
    have hF : (algebraMap (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) (LaurentSeries (ResidueField ↥A))).comp
          ((algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).comp (IsLocalRing.residue ↥A)) =
        (qExpand (ResidueField ↥A) p).comp ((algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))).comp
          (IsLocalRing.residue ↥A)) := by
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply, algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]
    rw [hX, hF]
  intro h0
  have h0' := congrArg (fun z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) => (z : LaurentSeries (ResidueField ↥A))) h0
  simp only [ZeroMemClass.coe_zero] at h0'
  rw [hcoe] at h0'
  have hne : Polynomial.eval₂ (algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A))) (jqModC (ResidueField ↥A))
      (Q.map (IsLocalRing.residue ↥A)) ≠ 0 := by
    intro hz
    exact ModularCurve.transcendental_jqModC (ResidueField ↥A) ⟨Q.map (IsLocalRing.residue ↥A), hQ, hz⟩
  exact qExpand_ne_zero p hne h0'

theorem x_facts
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∃ h : x ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨x, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) ∧
      Rpd.R₁.residue ⟨x, h⟩ ≠ 0 := by
  have hcoe : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (jqModC ↥A) := by
    rw [hx, coeffMap_jqModC]
  obtain ⟨h, hres⟩ := mem₁_and_residue_of_coe_eq p M H hpM A θ Psp Rpd x _ hcoe
  rw [coeffMap_jqModC] at hres
  refine ⟨h, hres, fun h0 => ?_⟩
  have := congrArg (fun z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) => (z : LaurentSeries (ResidueField ↥A))) h0
  simp only [ZeroMemClass.coe_zero] at this
  rw [hres] at this
  exact ModularCurve.jqModC_ne_zero_def (ResidueField ↥A) this

theorem jp_facts
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (jp : ↥(xHFunctionFieldBar M H))
    (hjp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((jp : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ h : jp ∈ Rpd.R₁.integers,
      ((Rpd.R₁.residue ⟨jp, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
          qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)) ∧
      ((Rpd.R₁.residue ⟨jp, h⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = (jqModC (ResidueField ↥A)) ^ p ∧
      Rpd.R₁.residue ⟨jp, h⟩ ≠ 0 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcoe : ((jp : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap A.subtype (qExpand ↥A p (jqModC ↥A)) := by
    rw [hjp, coeffMap_qExpand, coeffMap_jqModC]
  obtain ⟨h, hres⟩ := mem₁_and_residue_of_coe_eq p M H hpM A θ Psp Rpd jp _ hcoe
  rw [coeffMap_qExpand, coeffMap_jqModC] at hres
  have hres' := hres
  rw [ModularCurve.qExpand_jqModC_eq_pow_unconditional] at hres'
  refine ⟨h, hres, hres', fun h0 => ?_⟩
  have := congrArg (fun z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) => (z : LaurentSeries (ResidueField ↥A))) h0
  simp only [ZeroMemClass.coe_zero] at this
  rw [hres'] at this
  exact pow_ne_zero p (ModularCurve.jqModC_ne_zero_def (ResidueField ↥A)) this

theorem exists_alpha_eq (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H))
    (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ∃ x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)), α x' = x := by
  have hj' : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))
    exact qExpFunctionFieldC_mono ℚ le_top hj
  have hmem : jqModC (AlgebraicClosure ℚ) ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) := by
    have h := coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) hj'
    have he : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := coeffMap_jqModC _
    rw [he] at h
    exact h
  refine ⟨⟨jqModC (AlgebraicClosure ℚ), hmem⟩, Subtype.ext ?_⟩
  rw [hα_coe, hx]

theorem exists_sigmaBar
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (jp : ↥(xHFunctionFieldBar M H))
    (hjp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((jp : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) :
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∃ σb : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H),
      (∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((σb (α u) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ))) ∧
      σb x = jp ∧ σb jp = x := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨σ, hσ₁, hσ₂⟩ : ∃ σ : ↥(xHFunctionField M H) ≃ₐ[ℚ] ↥(xHFunctionField M H),
      (∀ (f : ↥(xHFunctionField M H)) (u : ↥(xHFunctionField (M / p) (infSubgroup p M H hpM))),
          (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
            ((σ f : ↥(xHFunctionField M H)) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ)) ∧
      (∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
          ∀ (f : ↥(xHFunctionField M H)) (u : ↥(xHFunctionField (M / p) (infSubgroup p M H hpM))),
            (f : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ) →
              coeffEmb (AlgebraicClosure ℚ) ((σ f : ↥(xHFunctionField M H)) : LaurentSeries ℚ) =
                ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c
                    ⟨coeffEmb (AlgebraicClosure ℚ) (u : LaurentSeries ℚ),
                      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) u.2⟩ :
                    ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
                  LaurentSeries (AlgebraicClosure ℚ))) :=
    ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  let σb : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H) :=
    geomAut (AlgebraicClosure ℚ) (xHFunctionField M H) σ
  have hle : xHFunctionField (M / p) (infSubgroup p M H hpM) ≤ xHFunctionField M H :=
    qExpFunctionFieldC_mono ℚ (ModularCurve.GammaH_le_GammaH_div_infSubgroup p M H hpM)
  have hj' : jqModC ℚ ∈ xHFunctionField (M / p) (infSubgroup p M H hpM) := by
    show jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH (M / p) (infSubgroup p M H hpM))
    exact qExpFunctionFieldC_mono ℚ le_top hj
  have hmono : ∀ z, z ∈ xHFunctionFieldBar (M / p) (infSubgroup p M H hpM) → z ∈ xHFunctionFieldBar M H := by
    intro z hz
    have h2 := (α ⟨z, hz⟩).2
    rw [hα_coe] at h2
    exact h2

  have hgen : ∀ (y : LaurentSeries ℚ) (hy : y ∈ xHFunctionField (M / p) (infSubgroup p M H hpM)),
      ((σb ⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hle hy)⟩ : ↥(xHFunctionFieldBar M H)) :
        LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) y) := by
    intro y hy
    have e := coe_geomAut_coeffEmb (AlgebraicClosure ℚ) (xHFunctionField M H) σ ⟨y, hle hy⟩
    have e2 := hσ₁ ⟨y, hle hy⟩ ⟨y, hy⟩ rfl
    have e3 : (⟨coeffEmb (AlgebraicClosure ℚ) y, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hle hy)⟩ : ↥(xHFunctionFieldBar M H)) =
        ⟨coeffEmb (AlgebraicClosure ℚ) ((⟨y, hle hy⟩ : ↥(xHFunctionField M H)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (⟨y, hle hy⟩ : ↥(xHFunctionField M H)).2⟩ := rfl
    rw [e3]
    show ((geomAut (AlgebraicClosure ℚ) (xHFunctionField M H) σ _ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [e, e2]
    show coeffMap _ (qExpand ℚ p y) = qExpand (AlgebraicClosure ℚ) p (coeffMap _ y)
    exact coeffMap_qExpand _ p y

  have hσα : ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((σb (α u) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) := by
    intro u
    have hαu : α u = ⟨(u : LaurentSeries (AlgebraicClosure ℚ)), hmono _ u.2⟩ := Subtype.ext (hα_coe u)
    rw [hαu]
    exact coe_apply_eq_qExpand_of_mem p M H hpM σb hle hgen (u : LaurentSeries (AlgebraicClosure ℚ)) u.2 _

  set j₀ : ↥(xHFunctionField M H) := ⟨jqModC ℚ, hle hj'⟩ with hj₀
  have hxe : x = ⟨coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ), coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (hle hj')⟩ :=
    Subtype.ext (by rw [hx]; exact (coeffMap_jqModC _).symm)
  have hσj₀ : ((σ j₀ : ↥(xHFunctionField M H)) : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ) := hσ₁ j₀ ⟨jqModC ℚ, hj'⟩ rfl

  have hσx : σb x = jp := by
    apply Subtype.ext
    rw [hxe, hgen (jqModC ℚ) hj', hjp]
    show qExpand (AlgebraicClosure ℚ) p (coeffMap _ (jqModC ℚ)) = _
    rw [coeffMap_jqModC]

  have hcop : Nat.Coprime p (M / p) := by
    rw [Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)]
    intro hd
    apply hpM2
    obtain ⟨k, hk⟩ := hd
    refine ⟨k, ?_⟩
    calc M = p * (M / p) := (Nat.mul_div_cancel' hpM).symm
      _ = p ^ 2 * k := by rw [hk]; ring
  set c : (ZMod (M / p))ˣ := ZMod.unitOfCoprime p hcop with hc
  have hcp : (c : ZMod (M / p)) = (p : ZMod (M / p)) := ZMod.coe_unitOfCoprime p hcop
  have hjpe : jp = ⟨coeffEmb (AlgebraicClosure ℚ) ((σ j₀ : ↥(xHFunctionField M H)) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (σ j₀).2⟩ := by
    apply Subtype.ext
    show ((jp : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffMap _ ((σ j₀ : ↥(xHFunctionField M H)) : LaurentSeries ℚ)
    rw [hjp, hσj₀, coeffMap_qExpand, coeffMap_jqModC]
  have hσjp : σb jp = x := by
    apply Subtype.ext
    rw [hjpe]
    show ((geomAut (AlgebraicClosure ℚ) (xHFunctionField M H) σ _ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = _
    rw [coe_geomAut_coeffEmb, hσ₂ c hcp (σ j₀) ⟨jqModC ℚ, hj'⟩ hσj₀,
      ModularCurve.diamondAutHBar_apply_eq_self_of_coe_eq_coeffEmb_of_mem_gamma0 (M / p) (infSubgroup p M H hpM) c _ (jqModC ℚ)
        (qExpFunctionFieldC_mono ℚ le_top hj) rfl, hx]
    exact coeffMap_jqModC _
  exact ⟨σb, hσα, hσx, hσjp⟩

theorem valuation_lt_one_map_of_forall_mem_iff {F : Type*} [Field F] (O₁ O₂ : ValuationSubring F) (e : F ≃+* F)
    (h : ∀ g, g ∈ O₂ ↔ e g ∈ O₁) {g : F} (hg : O₂.valuation g < 1) : O₁.valuation (e g) < 1 := by
  by_cases hg0 : g = 0
  · subst hg0
    rw [map_zero, map_zero]
    exact zero_lt_one
  · rw [valuation_lt_one_iff_inv_not_mem O₂ hg0] at hg
    rw [valuation_lt_one_iff_inv_not_mem O₁ ((map_ne_zero_iff e e.injective).mpr hg0), ← map_inv₀, ← h]
    exact hg

theorem integers_snd_eq_comap
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
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (jp : ↥(xHFunctionFieldBar M H))
    (hjp : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((jp : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)))
    (σb : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hσα : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
        ((σb (α u) : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hσx : σb x = jp) :
    Rpd.R₂.integers = Rpd.R₁.integers.comap σb.toAlgHom.toRingHom := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set O := Rpd.R₁.integers.comap σb.toAlgHom.toRingHom with hOdef
  have hmemO : ∀ f, f ∈ O ↔ σb f ∈ Rpd.R₁.integers := fun f => ValuationSubring.mem_comap
  obtain ⟨-, hcomplete, -⟩ :=
    ModularCurve.XHDRModelAtP.integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen α hα_coe Psp Rpd hres₂α x hx

  have hconst : ∀ c : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) c ∈ O ↔ c ∈ A := by
    intro c
    rw [hmemO, AlgEquiv.commutes]
    exact Rpd.R₁.algebraMap_mem_iff c

  obtain ⟨hjp1, hresjp, -, -⟩ := jp_facts p M H hpM A θ Psp Rpd jp hjp
  have hgenO : ∀ Q : Polynomial ↥A, Q.map (IsLocalRing.residue ↥A) ≠ 0 →
      Polynomial.aeval x (Q.map A.subtype) ∈ O ∧ (Polynomial.aeval x (Q.map A.subtype))⁻¹ ∈ O := by
    intro Q hQ
    have hq := aeval_mem_and_inv_mem_of_residue_eq_qExpand p M H hpM A Rpd.R₁ jp hjp1 hresjp Q hQ
    have e : σb (Polynomial.aeval x (Q.map A.subtype)) = Polynomial.aeval jp (Q.map A.subtype) := by
      rw [← hσx, ← AlgEquiv.coe_algHom, ← Polynomial.aeval_algHom_apply]
    refine ⟨?_, ?_⟩
    · rw [hmemO, e]; exact hq.1
    · rw [hmemO, map_inv₀, e]; exact hq.2
  rcases hcomplete O hconst hgenO with hO | hO
  ·
    exfalso
    have hstab : ∀ g, g ∈ Rpd.R₁.integers ↔ σb g ∈ Rpd.R₁.integers := fun g => by rw [← hmemO, hO]
    obtain ⟨hx1, hresx, -⟩ := x_facts p M H hpM A θ Psp Rpd x hx

    have hg₀ : σb.symm x ∈ Rpd.R₁.integers := (hstab _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact hx1)
    obtain ⟨-, hsep⟩ := ModularCurve.JHPlaceSpecialization.ProlongationDatum.integers_fst_isGeneric_and_forall_exists_valuation_sub_alpha_lt_one
      p M H hpM hpM2 hHp A hA θ Psp Rpd α hα_coe x hx
    obtain ⟨u, hu₁, hval⟩ := hsep (σb.symm x) hg₀
    obtain ⟨hσu, hresσu⟩ := key₁ p M H hpM hpM2 hHp A hA θ Psp Rpd α hα_coe σb hσα u hu₁

    have hval' : Rpd.R₁.integers.valuation (σb (σb.symm x - α u)) < 1 :=
      valuation_lt_one_map_of_forall_mem_iff Rpd.R₁.integers Rpd.R₁.integers σb.toRingEquiv hstab hval
    rw [map_sub, AlgEquiv.apply_symm_apply] at hval'
    have hsubmem : x - σb (α u) ∈ Rpd.R₁.integers := sub_mem hx1 hσu
    have hres0 : Rpd.R₁.residue ⟨x - σb (α u), hsubmem⟩ = 0 := (residue_eq_zero_iff Rpd.R₁ _ hsubmem).mpr hval'
    have hsub : (⟨x - σb (α u), hsubmem⟩ : ↥Rpd.R₁.integers) = ⟨x, hx1⟩ - ⟨σb (α u), hσu⟩ := Subtype.ext (by simp)
    rw [hsub, map_sub, sub_eq_zero] at hres0
    have hc := congrArg (fun z : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) => (z : LaurentSeries (ResidueField ↥A)).coeff (-1 : ℤ)) hres0
    beta_reduce at hc
    rw [hresx, hresσu, ModularCurve.coeff_jqModC_neg_one, qExpand_coeff_of_not_dvd] at hc
    · exact one_ne_zero hc
    · intro hd
      exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp (Int.dvd_neg.mp hd)))
  · exact hO.symm

set_option maxHeartbeats 6400000 in
theorem core
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
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))
    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p) :
    ∃ h₂ : t ∈ Rpd.R₂.integers,
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Rpd.R₂.residue ⟨t, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) =
        jqModC (ResidueField ↥A) * ((qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)))⁻¹) ^ p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  obtain ⟨x', rfl⟩ := exists_alpha_eq p M H hpM hj α hα_coe x hx
  have hx0 : (α x') ≠ 0 := by
    intro h
    have h' := congrArg (fun z : ↥(xHFunctionFieldBar M H) => (z : LaurentSeries (AlgebraicClosure ℚ))) h
    simp only [ZeroMemClass.coe_zero] at h'
    rw [hx] at h'
    exact ModularCurve.jqModC_ne_zero_def (AlgebraicClosure ℚ) h'

  set jp : ↥(xHFunctionFieldBar M H) := t * (α x') ^ p with hjpdef
  have hjp : ((jp : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := by
    rw [hjpdef, MulMemClass.coe_mul, SubmonoidClass.coe_pow, ht, hx, mul_assoc, ← mul_pow,
      inv_mul_cancel₀ (ModularCurve.jqModC_ne_zero_def (AlgebraicClosure ℚ)), one_pow, mul_one]
  have htj : t = jp * ((α x') ^ p)⁻¹ := by rw [hjpdef, mul_inv_cancel_right₀ (pow_ne_zero p hx0)]

  obtain ⟨σb, hσα, hσx, hσjp⟩ := exists_sigmaBar p M H hpM hpM2 hHp hj α hα_coe (α x') hx jp hjp
  have hR₂ := integers_snd_eq_comap p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen Psp Rpd α hα_coe hres₂α (α x') hx jp hjp σb hσα hσx
  have hmem₂ : ∀ f, f ∈ Rpd.R₂.integers ↔ σb f ∈ Rpd.R₁.integers := by
    intro f; rw [hR₂]; exact ValuationSubring.mem_comap
  obtain ⟨hx1, hresx, hJne⟩ := x_facts p M H hpM A θ Psp Rpd (α x') hx
  obtain ⟨hjp1, hresjp, hresjp', hJpne⟩ := jp_facts p M H hpM A θ Psp Rpd jp hjp

  have hx₂ : α x' ∈ Rpd.R₂.integers := (hmem₂ (α x')).mpr (by rw [hσx]; exact hjp1)
  have hres₂x : Rpd.R₂.residue ⟨α x', hx₂⟩ = (Rpd.R₁.residue ⟨α x', hx1⟩) ^ p := by
    have e := hres₂α x' hx1 hx₂

    apply Subtype.ext
    show ((Rpd.R₂.residue ⟨α x', hx₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
      (((Rpd.R₁.residue ⟨α x', hx1⟩) ^ p : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A))
    rw [e, coe_qExpFrobeniusModL, hresx, SubmonoidClass.coe_pow, hresx, ModularCurve.qExpand_jqModC_eq_pow_unconditional]

  have hjpinv : jp⁻¹ ∈ Rpd.R₁.integers := inv_mem_of_residue_ne_zero Rpd.R₁ jp hjp1 hJpne
  have hσt : σb t = (α x') * (jp⁻¹) ^ p := by rw [htj, map_mul, map_inv₀, map_pow, hσjp, hσx, inv_pow]
  have hσt1 : σb t ∈ Rpd.R₁.integers := by rw [hσt]; exact mul_mem hx1 (pow_mem hjpinv p)
  have ht₂ : t ∈ Rpd.R₂.integers := (hmem₂ t).mpr hσt1
  refine ⟨ht₂, ?_⟩

  let σr : ↥Rpd.R₂.integers →+* ↥Rpd.R₁.integers :=
    (σb.toAlgHom.toRingHom).restrict Rpd.R₂.integers Rpd.R₁.integers (fun f hf => (hmem₂ f).mp hf)
  have σr_apply : ∀ f : ↥Rpd.R₂.integers, σr f = ⟨σb f, (hmem₂ f).mp f.2⟩ := fun f => rfl
  let ψ : ↥Rpd.R₂.integers →+* JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) := Rpd.R₁.residue.comp σr
  have ψ_apply : ∀ f : ↥Rpd.R₂.integers, ψ f = Rpd.R₁.residue ⟨σb f, (hmem₂ f).mp f.2⟩ := fun f => rfl
  have hψsurj : Function.Surjective ψ := by
    intro b
    obtain ⟨a, ha⟩ := Rpd.R₁.residue_surjective b
    have hmem : σb.symm (a : ↥(xHFunctionFieldBar M H)) ∈ Rpd.R₂.integers :=
      (hmem₂ _).mpr (by rw [AlgEquiv.apply_symm_apply]; exact a.2)
    refine ⟨⟨σb.symm a, hmem⟩, ?_⟩
    rw [ψ_apply, ← ha]
    congr 1
    exact Subtype.ext (AlgEquiv.apply_symm_apply σb a)
  have hsymm : ∀ g, g ∈ Rpd.R₁.integers ↔ σb.symm.toRingEquiv g ∈ Rpd.R₂.integers := by
    intro g
    rw [hmem₂]
    show _ ↔ σb (σb.symm g) ∈ _
    rw [AlgEquiv.apply_symm_apply]
  have hker : RingHom.ker ψ ≤ RingHom.ker Rpd.R₂.residue := by
    intro f hf
    rw [RingHom.mem_ker] at hf ⊢
    rw [ψ_apply] at hf
    have h1 : Rpd.R₁.integers.valuation (σb f) < 1 := (residue_eq_zero_iff Rpd.R₁ _ _).mp hf
    have h2 := valuation_lt_one_map_of_forall_mem_iff Rpd.R₂.integers Rpd.R₁.integers σb.symm.toRingEquiv hsymm h1
    have h3 : Rpd.R₂.integers.valuation (f : ↥(xHFunctionFieldBar M H)) < 1 := by
      have : σb.symm.toRingEquiv (σb f) = f := AlgEquiv.symm_apply_apply σb f
      rw [this] at h2
      exact h2
    have := (residue_eq_zero_iff Rpd.R₂ _ f.2).mpr h3
    simpa using this
  let τ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) →+* JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) :=
    ψ.liftOfSurjective hψsurj ⟨Rpd.R₂.residue, hker⟩
  have hτψ : ∀ f : ↥Rpd.R₂.integers, τ (ψ f) = Rpd.R₂.residue f := fun f =>
    RingHom.liftOfRightInverse_comp_apply ψ _ _ ⟨Rpd.R₂.residue, hker⟩ f

  have hJp : (Rpd.R₁.residue ⟨jp, hjp1⟩) = (Rpd.R₁.residue ⟨(α x'), hx1⟩) ^ p := by
    apply Subtype.ext
    rw [hresjp', SubmonoidClass.coe_pow, hresx]

  have hψx : ψ ⟨(α x'), hx₂⟩ = (Rpd.R₁.residue ⟨jp, hjp1⟩) := by
    rw [ψ_apply]
    congr 1
    exact Subtype.ext hσx
  haveI : CharP (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) p :=
    charP_of_injective_algebraMap (algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))).injective p
  have hτJ : τ (Rpd.R₁.residue ⟨(α x'), hx1⟩) = (Rpd.R₁.residue ⟨(α x'), hx1⟩) := by
    have h1 : τ (Rpd.R₁.residue ⟨jp, hjp1⟩) = (Rpd.R₁.residue ⟨(α x'), hx1⟩) ^ p := by rw [← hψx, hτψ]; exact hres₂x
    rw [hJp, map_pow] at h1
    exact frobenius_inj _ p h1
  have hτJp : τ (Rpd.R₁.residue ⟨jp, hjp1⟩) = (Rpd.R₁.residue ⟨jp, hjp1⟩) := by rw [hJp, map_pow, hτJ]

  have hresinv : Rpd.R₁.residue ⟨jp⁻¹, hjpinv⟩ = (Rpd.R₁.residue ⟨jp, hjp1⟩)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    have : (⟨jp⁻¹, hjpinv⟩ : ↥Rpd.R₁.integers) * ⟨jp, hjp1⟩ = 1 := by
      apply Subtype.ext
      show jp⁻¹ * jp = 1
      exact inv_mul_cancel₀ (fun h => hJpne (by
        have : (⟨jp, hjp1⟩ : ↥Rpd.R₁.integers) = 0 := Subtype.ext h
        rw [this, map_zero]))
    rw [this, map_one]

  have hψt : ψ ⟨t, ht₂⟩ = (Rpd.R₁.residue ⟨(α x'), hx1⟩) * ((Rpd.R₁.residue ⟨jp, hjp1⟩)⁻¹) ^ p := by
    rw [ψ_apply]
    have : (⟨σb t, (hmem₂ t).mp ht₂⟩ : ↥Rpd.R₁.integers) = ⟨(α x'), hx1⟩ * (⟨jp⁻¹, hjpinv⟩) ^ p :=
      Subtype.ext (by simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]; exact hσt)
    rw [this, map_mul, map_pow, hresinv]
  have hres₂t : Rpd.R₂.residue ⟨t, ht₂⟩ = (Rpd.R₁.residue ⟨(α x'), hx1⟩) * ((Rpd.R₁.residue ⟨jp, hjp1⟩)⁻¹) ^ p := by
    rw [← hτψ, hψt, map_mul, map_pow, map_inv₀, hτJ, hτJp]
  show ((Rpd.R₂.residue ⟨t, ht₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = _
  rw [hres₂t]
  push_cast
  rw [hresx, hresjp]

end Res2T

set_option synthInstance.maxHeartbeats 1600000 in

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

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (x : ↥(xHFunctionFieldBar M H)) (hx : ((x : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))

    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p) :
    ∃ h₂ : t ∈ Rpd.R₂.integers,
      haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((Rpd.R₂.residue ⟨t, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) : LaurentSeries (ResidueField ↥A)) =
        jqModC (ResidueField ↥A) * ((qExpand (ResidueField ↥A) p (jqModC (ResidueField ↥A)))⁻¹) ^ p := by
  exact Res2T.core p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen Psp Rpd α hα_coe hres₂α x hx t ht

#print axioms solution

end S_ModularCurve_XHDRModelAtP_exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL (solution)
