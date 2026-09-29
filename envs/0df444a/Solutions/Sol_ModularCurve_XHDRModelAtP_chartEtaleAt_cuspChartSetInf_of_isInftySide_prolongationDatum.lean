-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.chartEtaleAt_cuspChartSetInf_of_isInftySide_prolongationDatum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/dda5fe42-32d5-5e55-bece-dc5328ff796c

import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL
import Theorems.Thm_ModularCurve_ModularPolynomialData_exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar
import Theorems.Thm_ModularCurve_XHDRLevel_exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add
import Theorems.Thm_ModularCurve_XHDRModelAtP_not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_ModularCurve_exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_JHChartSemicontinuity
import Definitions.Def_ModularCurve_JHCuspChartSet
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_chartEtaleAt_cuspChartSetInf_of_isInftySide_prolongationDatum
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions"
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

open scoped MatrixGroups

namespace Ws47
namespace D3c
open ModularCurve AlgebraicCurve

theorem coeffMap_qExpand {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (g : LaurentSeries R) : coeffMap f (qExpand R N g) = qExpand S N (coeffMap f g) := by
  ext k
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd (N := N) g hk, qExpand_coeff_of_not_dvd (N := N) (coeffMap f g) hk, map_zero]

theorem hasValue_add {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g g' : F} {c c' : K} (h : u.HasValue g c) (h' : u.HasValue g' c') : u.HasValue (g + g') (c + c') := by
  obtain ⟨hg, hr⟩ := h
  obtain ⟨hg', hr'⟩ := h'
  refine ⟨add_mem hg hg', ?_⟩
  have : (⟨g + g', add_mem hg hg'⟩ : u.toValuationSubring) = ⟨g, hg⟩ + ⟨g', hg'⟩ := rfl
  rw [this, map_add, hr, hr', map_add]

theorem hasValue_pow {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (n : ℕ) : u.HasValue (g ^ n) (c ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact u.hasValue_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem hasValue_eval₂_int {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} {c : K} (h : u.HasValue g c) (P : Polynomial ℤ) :
    u.HasValue (P.eval₂ (Int.castRingHom F) g) (P.eval₂ (Int.castRingHom K) c) := by
  induction P using Polynomial.induction_on' with
  | add f g' hf hg' => rw [Polynomial.eval₂_add, Polynomial.eval₂_add]; exact hasValue_add u hf hg'
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial]
    have hc : u.HasValue ((Int.castRingHom F) a) ((Int.castRingHom K) a) := by
      have := u.hasValue_algebraMap ((a : ℤ) : K)
      rwa [map_intCast] at this
    exact hc.mul (hasValue_pow u h n)

theorem hasValue_eval₂_eval₂_int {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g w : F} {c d : K} (hg : u.HasValue g c) (hw : u.HasValue w d) (P : Polynomial (Polynomial ℤ)) :
    u.HasValue (P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom F) g) w)
      (P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom K) c) d) := by
  induction P using Polynomial.induction_on' with
  | add f g' hf hg' => rw [Polynomial.eval₂_add, Polynomial.eval₂_add]; exact hasValue_add u hf hg'
  | monomial n a =>
    rw [Polynomial.eval₂_monomial, Polynomial.eval₂_monomial, Polynomial.coe_eval₂RingHom, Polynomial.coe_eval₂RingHom]
    exact (hasValue_eval₂_int u hg a).mul (hasValue_pow u hw n)

theorem eval_one_derivative_X_pow_mul (R : Type*) [CommRing R] (p : ℕ) :
    (Polynomial.derivative ((Polynomial.X : Polynomial R) ^ p * (Polynomial.X - 1))).eval 1 = 1 := by
  simp [Polynomial.derivative_mul]

theorem mem_nonunits_iff_eq_zero_or_inv_not_mem {K : Type*} [Field K] (A : ValuationSubring K) (x : K) :
    x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Valuation.val_lt_one_iff _ hx, ← ValuationSubring.valuation_le_one_iff, not_le]
    simp [hx]

theorem hasValue_inv_zero_of_not_mem {K F : Type*} [Field K] [Field F] [Algebra K F] (u : Place K F)
    {g : F} (hg : g ∉ u.toValuationSubring) : u.HasValue g⁻¹ 0 := by
  have h : g⁻¹ ∈ u.toValuationSubring.nonunits :=
    (mem_nonunits_iff_eq_zero_or_inv_not_mem _ _).mpr (Or.inr (by rwa [inv_inv]))
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  exact ⟨hmem, by rw [map_zero]; exact (IsLocalRing.residue_eq_zero_iff _).mpr hmax⟩

end Ws47.D3c

namespace Ws47
namespace D3c
open ModularCurve AlgebraicCurve ModularCurve.XHDRLevel IsLocalRing

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem kronecker_root
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (data : ModularPolynomialData p) (Q : Polynomial (Polynomial ℤ))
    (hQroot : ∀ (S : Type) [Field S] (x y : S), x ≠ 0 →
      data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x) y = 0 →
      Q.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom S) x⁻¹) (y / x ^ p) = 0) :
    ((Q.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) x'⁻¹)).map α.toRingHom).eval t = 0 := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hjcoe : ((α x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hα_coe, hx']
  have hjq0 : jqModC (AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have h1 := ModularCurve.coeff_jqModC_neg_one (AlgebraicClosure ℚ)
    rw [h, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1
  have hj0 : α x' ≠ 0 := by
    intro h; apply hjq0; rw [← hjcoe, h]; rfl
  let ev : Polynomial ℤ →+* ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Polynomial.eval₂RingHom (Int.castRingHom _) x'⁻¹
  let m : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Q.map ev
  show (m.map α.toRingHom).eval t = 0
  rw [Polynomial.eval_map]
  show (Q.map ev).eval₂ α.toRingHom t = 0
  have hcomp : α.toRingHom.comp ev =
      (Polynomial.eval₂RingHom (Int.castRingHom ↥(xHFunctionFieldBar M H)) (α x')⁻¹ : Polynomial ℤ →+* ↥(xHFunctionFieldBar M H)) :=
    Polynomial.ringHom_ext (fun n => by simp [ev]) (by simp [ev, map_inv₀])
  rw [Polynomial.eval₂_map, hcomp, ← mul_div_cancel_right₀ t (pow_ne_zero p hj0)]
  refine hQroot ↥(xHFunctionFieldBar M H) (α x') (t * (α x') ^ p) hj0 ?_

  have hval : (((data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(xHFunctionFieldBar M H)) (α x')) (t * (α x') ^ p) :
      ↥(xHFunctionFieldBar M H))) : LaurentSeries (AlgebraicClosure ℚ)) =
      data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ)))
        (qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) := by
    rw [show (((data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(xHFunctionFieldBar M H)) (α x')) (t * (α x') ^ p) :
        ↥(xHFunctionFieldBar M H))) : LaurentSeries (AlgebraicClosure ℚ)) =
        (xHFunctionFieldBar M H).val.toRingHom (data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(xHFunctionFieldBar M H)) (α x')) (t * (α x') ^ p)) from rfl,
      Polynomial.hom_eval₂]
    congr 1
    · refine Polynomial.ringHom_ext (fun n => by simp) ?_
      simp [hjcoe]
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, IntermediateField.coe_val, map_mul, map_pow]
      rw [ht, hjcoe, mul_assoc, ← mul_pow, inv_mul_cancel₀ hjq0, one_pow, mul_one]
  have hrat : data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ)))
        (qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ))) = 0 := by
    have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
    rw [map_zero, Polynomial.hom_eval₂] at h0
    have hj' : coeffEmb (AlgebraicClosure ℚ) jq = jqModC (AlgebraicClosure ℚ) := map_jqModC _
    have hc : (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ =
        Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (AlgebraicClosure ℚ))) (jqModC (AlgebraicClosure ℚ)) :=
      Polynomial.ringHom_ext (fun n => by simp) (by simp [evalAtJ_X, hj'])
    rw [hc, jqN, show coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq) = qExpand (AlgebraicClosure ℚ) p (coeffEmb (AlgebraicClosure ℚ) jq)
      from Ws47.D3c.coeffMap_qExpand _ _ _, hj'] at h0
    exact h0
  rw [hrat] at hval
  exact_mod_cast hval

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem adjoin_range_union_eq_top
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (m : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hm : m.Monic) (hmd : m.natDegree = p + 1) (hroot : (m.map α.toRingHom).eval t = 0) :
    IntermediateField.adjoin (AlgebraicClosure ℚ) (Set.range α ∪ {t}) = ⊤ := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hjcoe : ((α x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hα_coe, hx']
  have hjq0 : jqModC (AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have h1 := ModularCurve.coeff_jqModC_neg_one (AlgebraicClosure ℚ)
    rw [h, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1
  have hj0 : α x' ≠ 0 := by
    intro h; apply hjq0; rw [← hjcoe, h]; rfl
  letI := AlgebraicCurve.algebraAlong α
  have hxM : (((t * (α x') ^ p : ↥(xHFunctionFieldBar M H))) : LaurentSeries (AlgebraicClosure ℚ)) =
      qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) := by
    push_cast
    rw [ht, hjcoe, mul_assoc, ← mul_pow, inv_mul_cancel₀ hjq0, one_pow, mul_one]
  have hmt : m.eval₂ α.toRingHom ((t * (α x') ^ p) / (α x') ^ p) = 0 := by
    rw [mul_div_cancel_right₀ t (pow_ne_zero p hj0), ← Polynomial.eval_map]
    exact hroot
  obtain ⟨hmin, hdeg⟩ := ModularCurve.minpoly_div_pow_eq_and_natDegree_minpoly_eq_finrank_of_monic_of_coe_eq_xHFunctionFieldBar
    p M H hpM hpM2 hHp α hα_coe x' hx' (t * (α x') ^ p) hxM m hm hmd hmt
  rw [mul_div_cancel_right₀ t (pow_ne_zero p hj0)] at hmin hdeg
  have hfr : AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) α = p + 1 :=
    ModularCurve.finrankAlong_eq_add_one_of_coe_eq_xHFunctionFieldBar p M H hpM hpM2 hHp α hα_coe

  have hfin : Module.finrank ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) = p + 1 := hfr
  haveI : FiniteDimensional ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H) :=
    Module.finite_of_finrank_pos (by rw [hfin]; exact Nat.succ_pos _)
  have hint : IsIntegral ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) t := IsIntegral.of_finite _ t
  have hE : IntermediateField.adjoin ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ({t} : Set ↥(xHFunctionFieldBar M H)) = ⊤ := by
    apply IntermediateField.toSubalgebra_injective
    apply Subalgebra.toSubmodule_injective
    rw [IntermediateField.top_toSubalgebra, Algebra.top_toSubmodule]
    apply Submodule.eq_top_of_finrank_eq
    change Module.finrank _ ↥(IntermediateField.adjoin _ ({t} : Set ↥(xHFunctionFieldBar M H))) = _
    rw [IntermediateField.adjoin.finrank hint, hdeg]
    exact hfr.trans hfin.symm

  rw [eq_top_iff]
  intro f _
  have hf : f ∈ IntermediateField.adjoin ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ({t} : Set ↥(xHFunctionFieldBar M H)) := by
    rw [hE]; trivial
  have hf' : f ∈ Subfield.closure (Set.range (algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H)) ∪ {t}) := hf
  have hsub : Set.range (algebraMap ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) ↥(xHFunctionFieldBar M H)) ∪ {t} ⊆
      Set.range (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∪ (Set.range α ∪ {t}) := by
    rintro g (⟨u, rfl⟩ | hg)
    · exact Or.inr (Or.inl ⟨u, rfl⟩)
    · exact Or.inr (Or.inr hg)
  exact Subfield.closure_mono hsub hf'

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in

theorem alpha_coeff_mem_closure
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)) (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (t : ↥(xHFunctionFieldBar M H))
    (Q : Polynomial (Polynomial ℤ)) (i : ℕ) :
    α ((Q.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) x'⁻¹)).coeff i) ∈
      Subring.closure (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t) := by
  let ev : Polynomial ℤ →+* ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Polynomial.eval₂RingHom (Int.castRingHom _) x'⁻¹
  let m : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Q.map ev
  refine Subring.subset_closure (Set.mem_union_left _ ?_)
  refine ⟨m.coeff i, ?_, rfl⟩
  letI : Algebra ↥A ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    ((algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))).comp A.subtype).toAlgebra
  have hmem : m.coeff i ∈ Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) := by
    rw [Polynomial.coeff_map]
    show (Q.coeff i).eval₂ (Int.castRingHom _) x'⁻¹ ∈ _
    have hxmem : x'⁻¹ ∈ Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :=
      Algebra.subset_adjoin rfl
    refine Polynomial.induction_on (Q.coeff i) (fun a => ?_) (fun f g hf hg => ?_) (fun n a _ => ?_)
    · rw [Polynomial.eval₂_C]; exact Subalgebra.intCast_mem _ a
    · rw [Polynomial.eval₂_add]; exact add_mem hf hg
    · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      exact mul_mem (Subalgebra.intCast_mem _ a) (pow_mem hxmem _)
  show IsIntegral _ (m.coeff i)
  exact isIntegral_algebraMap (R := ↥(Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))))
    (A := ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (x := (⟨m.coeff i, hmem⟩ : Algebra.adjoin ↥A ({x'⁻¹} : Set ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))))

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem not_hasValue_residue_derivative_zero
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : ∃ c, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceFst α hα) c = v)
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p)
    (Q : Polynomial (Polynomial ℤ))
    (hQred : ∀ (R : Type) [CommRing R] [CharP R p],
      Q.map (Polynomial.eval₂RingHom (Int.castRingHom R) 0) = Polynomial.X ^ p * (Polynomial.X - 1)) :
    ∀ hD : (Polynomial.derivative ((Q.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) x'⁻¹)).map α.toRingHom)).eval t ∈ Rpd.R₁.integers,
      ¬ v.HasValue (Rpd.R₁.residue ⟨_, hD⟩) (0 : ResidueField ↥A) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hjcoe : ((α x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hα_coe, hx']
  have hjq0 : jqModC (AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have h1 := ModularCurve.coeff_jqModC_neg_one (AlgebraicClosure ℚ)
    rw [h, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1
  have hj0 : α x' ≠ 0 := by
    intro h; apply hjq0; rw [← hjcoe, h]; rfl
  let ev : Polynomial ℤ →+* ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Polynomial.eval₂RingHom (Int.castRingHom _) x'⁻¹
  let m : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Q.map ev
  show ∀ hD : (Polynomial.derivative (m.map α.toRingHom)).eval t ∈ Rpd.R₁.integers, ¬ v.HasValue (Rpd.R₁.residue ⟨_, hD⟩) 0
  intro hD

  have hRQ : (algebraMap ℚ (AlgebraicClosure ℚ)).comp (algebraMap (R p) ℚ) = A.subtype.comp ρ := by
    rw [hρ]; exact (IsScalarTower.algebraMap_eq (R p) ℚ (AlgebraicClosure ℚ)).symm

  have hYj : coeffMap A.subtype (jqModC ↥A) = ((α x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [hjcoe]; exact map_jqModC _
  have hYjmem : coeffMap A.subtype (jqModC ↥A) ∈ xHFunctionFieldBar M H := by rw [hYj]; exact (α x').2
  obtain ⟨hj1', hjres'⟩ := Rpd.residue₁_coeffMap (jqModC ↥A) hYjmem
  have eelj : (⟨coeffMap A.subtype (jqModC ↥A), hYjmem⟩ : ↥(xHFunctionFieldBar M H)) = α x' := Subtype.ext hYj
  have hjR : α x' ∈ Rpd.R₁.integers := eelj ▸ hj1'
  have hjres : ((Rpd.R₁.residue ⟨α x', hjR⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) =
      jqModC (ResidueField ↥A) := by
    have eint : (⟨α x', hjR⟩ : Rpd.R₁.integers) = ⟨_, hj1'⟩ := Subtype.ext eelj.symm
    rw [eint, hjres']; exact map_jqModC _

  obtain ⟨yI, hyI⟩ := (ModularCurve.exists_coeffMap_eq_coe_of_mem_chartAlg_twoChartIntegralModel_qExpFunctionFieldC
    (ΓM M H) p (jAt (ΓM M H) hj) (coe_jAt _ hj)).2 (TwoChartIntegralModel.jInvChartInf (R p) _ (jAt (ΓM M H) hj))
  have hcoeI : (((TwoChartIntegralModel.jInvChartInf (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj) :
      ↥(qExpFunctionFieldC ℚ (ΓM M H))) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (jqModC ℚ)⁻¹ := by
    rw [TwoChartIntegralModel.coe_jInvChartInf]
    push_cast
    rw [coe_jAt]
  have hYI : coeffMap A.subtype (coeffMap ρ yI) = (((α x')⁻¹ : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coeffMap_coeffMap, ← hRQ, ← coeffMap_coeffMap, hyI, hcoeI, map_inv₀]
    push_cast
    rw [hjcoe]
    congr 1
    exact map_jqModC _
  have hYImem : coeffMap A.subtype (coeffMap ρ yI) ∈ xHFunctionFieldBar M H := by rw [hYI]; exact ((α x')⁻¹).2
  obtain ⟨hI1', -⟩ := Rpd.residue₁_coeffMap (coeffMap ρ yI) hYImem
  have hIR : (α x')⁻¹ ∈ Rpd.R₁.integers := (Subtype.ext hYI : (⟨_, hYImem⟩ : ↥(xHFunctionFieldBar M H)) = (α x')⁻¹) ▸ hI1'
  have hIres : Rpd.R₁.residue ⟨(α x')⁻¹, hIR⟩ = (Rpd.R₁.residue ⟨α x', hjR⟩)⁻¹ := by
    have hmul : (⟨α x', hjR⟩ : Rpd.R₁.integers) * ⟨(α x')⁻¹, hIR⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hj0)
    have h1 := congrArg Rpd.R₁.residue hmul
    rw [map_mul, map_one] at h1
    exact (eq_inv_of_mul_eq_one_right h1)

  obtain ⟨tt, y, z, htt, hy, hyz⟩ :=
    ModularCurve.XHDRLevel.exists_chartAlgInf_coe_eq_qExpand_jqModC_mul_inv_pow_and_coeffMap_eq_one_add p M H hpM hj
  have hY : coeffMap A.subtype (coeffMap ρ y) = ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) := by
    rw [coeffMap_coeffMap, ← hRQ, ← coeffMap_coeffMap, hy, htt, map_mul, map_pow, map_inv₀, coeffMap_qExpand, ht]
    have hj' : coeffMap (algebraMap ℚ (AlgebraicClosure ℚ)) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
    rw [hj']
  have hYmem : coeffMap A.subtype (coeffMap ρ y) ∈ xHFunctionFieldBar M H := by rw [hY]; exact t.2
  obtain ⟨ht1', htres'⟩ := Rpd.residue₁_coeffMap (coeffMap ρ y) hYmem
  have eelt : (⟨coeffMap A.subtype (coeffMap ρ y), hYmem⟩ : ↥(xHFunctionFieldBar M H)) = t := Subtype.ext hY
  have htR : t ∈ Rpd.R₁.integers := eelt ▸ ht1'
  have htres : Rpd.R₁.residue ⟨t, htR⟩ = 1 := by
    have eint : (⟨t, htR⟩ : Rpd.R₁.integers) = ⟨_, ht1'⟩ := Subtype.ext eelt.symm
    apply Subtype.ext
    rw [eint, htres', coeffMap_coeffMap, hyz, map_add, map_one]
    have hsm : coeffMap ((IsLocalRing.residue ↥A).comp ρ) (((p : ℕ) : R p) • z) = 0 := by
      ext k
      rw [coeffMap_coeff, HahnSeries.coeff_smul, smul_eq_mul, map_mul, map_natCast, CharP.cast_eq_zero, zero_mul]
      rfl
    rw [hsm, add_zero]
    rfl

  set g : Polynomial ℤ →+* ↥(xHFunctionFieldBar M H) := Polynomial.eval₂RingHom (Int.castRingHom _) (α x')⁻¹ with hg
  have hmap : m.map α.toRingHom = Q.map g := by
    rw [Polynomial.map_map]
    congr 1
    exact Polynomial.ringHom_ext (fun n => by simp [ev, hg]) (by simp [ev, hg, map_inv₀])
  have hgR : ∀ P : Polynomial ℤ, g P ∈ Rpd.R₁.integers := by
    intro P
    rw [hg, Polynomial.coe_eval₂RingHom]
    refine Polynomial.induction_on P (fun a => ?_) (fun f f' hf hf' => ?_) (fun n a _ => ?_)
    · rw [Polynomial.eval₂_C]; exact intCast_mem _ a
    · rw [Polynomial.eval₂_add]; exact add_mem hf hf'
    · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow]
      exact mul_mem (intCast_mem _ a) (pow_mem hIR _)
  let g₁ : Polynomial ℤ →+* Rpd.R₁.integers := g.codRestrict Rpd.R₁.integers hgR
  have hD' : (Polynomial.derivative (m.map α.toRingHom)).eval t = (Polynomial.derivative Q).eval₂ g t := by
    rw [hmap, Polynomial.derivative_map, Polynomial.eval_map]
  have hsub : (⟨_, hD⟩ : Rpd.R₁.integers) = (Polynomial.derivative Q).eval₂ g₁ ⟨t, htR⟩ := by
    apply Subtype.ext
    show (Polynomial.derivative (m.map α.toRingHom)).eval t = Rpd.R₁.integers.subtype ((Polynomial.derivative Q).eval₂ g₁ ⟨t, htR⟩)
    rw [hD', Polynomial.hom_eval₂]
    rfl
  have hres_g : Rpd.R₁.residue.comp g₁ =
      Polynomial.eval₂RingHom (Int.castRingHom _) (Rpd.R₁.residue ⟨(α x')⁻¹, hIR⟩) := by
    refine Polynomial.ringHom_ext (fun n => (eq_intCast ((Rpd.R₁.residue.comp g₁).comp Polynomial.C) n).trans
      (eq_intCast ((Polynomial.eval₂RingHom (Int.castRingHom _) (Rpd.R₁.residue ⟨(α x')⁻¹, hIR⟩)).comp Polynomial.C) n).symm) ?_
    rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    congr 1
    apply Subtype.ext
    show g Polynomial.X = (α x')⁻¹
    rw [hg, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  have hresD : Rpd.R₁.residue ⟨_, hD⟩ =
      (Polynomial.derivative Q).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (Rpd.R₁.residue ⟨(α x')⁻¹, hIR⟩)) 1 := by
    rw [hsub, Polynomial.hom_eval₂, hres_g, htres]

  have hIval : v.HasValue (Rpd.R₁.residue ⟨(α x')⁻¹, hIR⟩) 0 := by
    obtain ⟨c, hc, hcv⟩ := hv
    have hna := ModularCurve.XHDRModelAtP.not_isAffinePlace_reduceFst_of_isInftySide_prolongationDatum p M H hpM hpM2 hHp hj 𝔛 A hA
      ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hcomp c hc
    rw [hcv] at hna
    have hnoval : ∀ a : ResidueField ↥A, ¬ v.HasValue (Rpd.R₁.residue ⟨α x', hjR⟩) a :=
      fun a h => hna ⟨_, a, hjres, h⟩
    have hnotmem : Rpd.R₁.residue ⟨α x', hjR⟩ ∉ v.toValuationSubring := by
      intro hmem
      obtain ⟨a, ha, -⟩ := v.exists_hasValue_of_surjective
        ((ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2
          (ResidueField ↥A)).2.2 v) hmem
      exact hnoval a ha
    rw [hIres]
    exact hasValue_inv_zero_of_not_mem v hnotmem
  have hval := hasValue_eval₂_eval₂_int v hIval (v.hasValue_one) (Polynomial.derivative Q)
  rw [← hresD] at hval
  have hone : (Polynomial.derivative Q).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (ResidueField ↥A)) 0) 1 = 1 := by
    rw [← Polynomial.eval_map, ← Polynomial.derivative_map, hQred (ResidueField ↥A)]
    exact eval_one_derivative_X_pow_mul _ p
  rw [hone] at hval
  intro h0
  exact one_ne_zero (hval.unique h0)

end Ws47.D3c

open Ws47.D3c in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))

    (hcomp : (∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y)))
    (v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hv : ∃ c, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) c ∧ (Psp.reduceFst α hα) c = v)
    (x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (hx' : ((x' : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ))
    (t : ↥(xHFunctionFieldBar M H))
    (ht : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ((t : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) =
        qExpand (AlgebraicClosure ℚ) p (jqModC (AlgebraicClosure ℚ)) * ((jqModC (AlgebraicClosure ℚ))⁻¹) ^ p) :
    Rpd.ChartEtaleAt α v (JHPlaceSpecialization.cuspChartSetInf (p := p) A α x' t) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData p
  obtain ⟨Q, hQm, hQd, hQroot, hQred⟩ :=
    ModularCurve.ModularPolynomialData.exists_monic_eval2_inv_div_pow_eq_zero_and_map_eq_X_pow_mul_X_sub_one.{0, 0} p data

  let ev : Polynomial ℤ →+* ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) :=
    Polynomial.eval₂RingHom (Int.castRingHom _) x'⁻¹
  let m : Polynomial ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) := Q.map ev

  have hjcoe : ((α x' : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hα_coe, hx']
  have hjq0 : jqModC (AlgebraicClosure ℚ) ≠ 0 := by
    intro h
    have h1 := ModularCurve.coeff_jqModC_neg_one (AlgebraicClosure ℚ)
    rw [h, HahnSeries.coeff_zero] at h1
    exact zero_ne_one h1
  have hx'0 : x' ≠ 0 := by
    intro h; apply hjq0; rw [← hx', h]; rfl
  have hj0 : α x' ≠ 0 := by
    intro h; apply hjq0; rw [← hjcoe, h]; rfl
  refine ⟨t, m, ?_, ?_, ?_, hQm.map ev, ?_, ?_, ?_, ?_⟩
  ·
    refine Set.mem_union_right _ ⟨0, ?_⟩
    simp
  ·
    obtain ⟨h₂, hres₂⟩ :=
      ModularCurve.XHDRModelAtP.exists_mem_integers_residue_eq_jqModC_mul_inv_qExpand_pow_of_residue_eq_qExpFrobeniusModL
        p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ θ hwgen Psp Rpd α hα_coe hres₂α (α x') hjcoe t ht
    refine ⟨h₂, (p : ℤ) ^ 2 - 1, ?_, ?_⟩
    · intro hdvd
      have h1 : (p : ℤ) ∣ 1 := by
        have := dvd_sub (dvd_pow_self (p : ℤ) two_ne_zero) hdvd
        rwa [sub_sub_cancel] at this
      have hp1 : (p : ℤ) = 1 := Int.eq_one_of_dvd_one (Int.natCast_nonneg p) h1
      exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast hp1)
    · rw [hres₂]
      set J : LaurentSeries (ResidueField ↥A) := jqModC (ResidueField ↥A) with hJ
      have hJ0 : J ≠ 0 := ModularCurve.jqModC_ne_zero_def _
      have hE0 : qExpand (ResidueField ↥A) p J ≠ 0 := by
        intro h; exact hJ0 (qExpand_injective (R := ResidueField ↥A) (N := p) (by rw [h, map_zero]))
      have hEinv0 : (qExpand (ResidueField ↥A) p J)⁻¹ ≠ 0 := inv_ne_zero hE0
      have hordE : (qExpand (ResidueField ↥A) p J).order = -(p : ℤ) := by
        rw [ModularCurve.order_qExpandC _ p hJ0, hJ, ModularCurve.order_jqModC_def]; ring
      have hordEinv : ((qExpand (ResidueField ↥A) p J)⁻¹).order = (p : ℤ) := by
        have h := HahnSeries.order_mul hE0 hEinv0
        rw [mul_inv_cancel₀ hE0, HahnSeries.order_one, hordE] at h
        omega
      have hprod0 : J * (qExpand (ResidueField ↥A) p J)⁻¹ ^ p ≠ 0 := mul_ne_zero hJ0 (pow_ne_zero _ hEinv0)
      have hord : (J * (qExpand (ResidueField ↥A) p J)⁻¹ ^ p).order = (p : ℤ) ^ 2 - 1 := by
        rw [HahnSeries.order_mul hJ0 (pow_ne_zero _ hEinv0), HahnSeries.order_pow, hordEinv, hJ, ModularCurve.order_jqModC_def]
        ring
      have h := HahnSeries.coeff_order_eq_zero.not.mpr hprod0
      rwa [hord] at h
  · exact adjoin_range_union_eq_top p M H hpM hpM2 hHp α hα_coe x' hx' t ht m (hQm.map ev) (by rw [hQm.natDegree_map]; exact hQd)
      (kronecker_root p M H hpM α hα_coe x' hx' t ht data Q hQroot)
  ·
    rw [hQm.natDegree_map]
    exact hQd
  · exact kronecker_root p M H hpM α hα_coe x' hx' t ht data Q hQroot
  · exact fun i => alpha_coeff_mem_closure p M H hpM A α x' t Q i
  · exact not_hasValue_residue_derivative_zero p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ θ hwgen α hα_coe hα hβ Psp Rpd hres₂α hcomp v hv x' hx' t ht Q hQred

end S_ModularCurve_XHDRModelAtP_chartEtaleAt_cuspChartSetInf_of_isInftySide_prolongationDatum
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_chartEtaleAt_cuspChartSetInf_of_isInftySide_prolongationDatum (solution)
