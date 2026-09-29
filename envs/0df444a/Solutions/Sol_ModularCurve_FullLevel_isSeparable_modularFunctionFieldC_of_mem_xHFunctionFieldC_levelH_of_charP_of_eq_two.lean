-- Prove2me | solution 1 for ModularCurve.FullLevel.isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/9fd296b4-d8f3-5766-91b2-621615009205

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gamma0_eq_qExpFunctionFieldC_gamma0_div_of_sq_dvd
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_two
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.baseAut_x1ArithFrobC_apply"
p2m_attr_erase "simp" "ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

noncomputable section

namespace IGSEP23

open scoped MatrixGroups
open ModularCurve ModularCurve.FullLevel CongruenceSubgroup

theorem unitsMap_neg {n m : ℕ} (h : n ∣ m) (u : (ZMod m)ˣ) : ZMod.unitsMap h (-u) = -ZMod.unitsMap h u := by
  ext
  simp [ZMod.unitsMap_def]

theorem mem_levelH_or_neg_mem (q : ℕ) (hpm : ∀ u : (ZMod q)ˣ, u = 1 ∨ u = -1) (M' : ℕ)
    (u : (ZMod (q ^ 2 * M'))ˣ) : u ∈ levelH q M' ∨ -u ∈ levelH q M' := by
  rcases hpm (ZMod.unitsMap (dvd_sq_mul q M') u) with h | h
  · exact Or.inl ((mem_levelH_iff q M' u).mpr h)
  · refine Or.inr ((mem_levelH_iff q M' (-u)).mpr ?_)
    rw [unitsMap_neg, h, neg_neg]

theorem mem_gammaH_or_neg_mem {N : ℕ} (H : Subgroup (ZMod N)ˣ) (hH : ∀ u : (ZMod N)ˣ, u ∈ H ∨ -u ∈ H)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) : γ ∈ CohCarrier.GammaH N H ∨ -γ ∈ CohCarrier.GammaH N H := by
  have hγ' : -γ ∈ Gamma0 N := by
    rw [Gamma0_mem] at hγ ⊢
    rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hγ, neg_zero]
  rcases hH (CohCarrier.gamma0Units N ⟨γ, hγ⟩) with h | h
  · exact Or.inl (CohCarrier.mem_GammaH_iff.mpr ⟨hγ, h⟩)
  · refine Or.inr (CohCarrier.mem_GammaH_iff.mpr ⟨hγ', ?_⟩)
    have : CohCarrier.gamma0Units N ⟨-γ, hγ'⟩ = -CohCarrier.gamma0Units N ⟨γ, hγ⟩ := by
      ext
      rw [Units.val_neg, CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
      show (((-γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = -(((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod N)
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg]
    rw [this]
    exact h

theorem xHFunctionFieldC_eq_gamma0 (K : Type*) [Field K] {N : ℕ} (H : Subgroup (ZMod N)ˣ)
    (hH : ∀ u : (ZMod N)ˣ, u ∈ H ∨ -u ∈ H) :
    xHFunctionFieldC K N H = qExpFunctionFieldC K (Gamma0 N) :=
  ModularCurve.qExpFunctionFieldC_eq_of_le_of_forall_mem_or_neg_mem K (CohCarrier.GammaH_le_Gamma0 H)
    (translation_mem_GammaH N H) (mem_gammaH_or_neg_mem H hH)

theorem qExpFunctionFieldC_gamma0_mul_le (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type*) [Field κ] [CharP κ q] :
    qExpFunctionFieldC κ (Gamma0 (q * M')) ≤ qExpFunctionFieldC κ (Gamma0 M') := by
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hdiv : q * M' / q = M' := Nat.mul_div_cancel_left M' hq0
  have h1 : q ∣ q * M' := dvd_mul_right q M'
  have h2 : ¬ q ^ 2 ∣ q * M' := fun h => hqM' (by
    rw [pow_two] at h
    exact (Nat.mul_dvd_mul_iff_left hq0).mp h)
  have step := ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup q (q * M')
    h1 h2 ⊤ (fun u _ => Subgroup.mem_top u) κ
  rw [CohCarrier.GammaH_top] at step
  refine step.trans (qExpFunctionFieldC_mono κ ?_)
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' : A ∈ Gamma0 (q * M' / q) := by rwa [hdiv]
  refine ⟨hA', ?_⟩
  rw [ModularCurve.mem_infSubgroup_iff]
  obtain ⟨d, hd⟩ := ZMod.unitsMap_surjective (Nat.div_dvd_of_dvd h1)
    (CohCarrier.gamma0Units (q * M' / q) ⟨A, hA'⟩)
  exact ⟨d, Subgroup.mem_top d, hd⟩

theorem xHFunctionFieldC_levelH_le (q : ℕ) [Fact q.Prime] (hpm : ∀ u : (ZMod q)ˣ, u = 1 ∨ u = -1)
    (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (κ : Type*) [Field κ] [CharP κ q] :
    xHFunctionFieldC κ (q ^ 2 * M') (levelH q M') ≤ modularFunctionFieldC κ M' := by
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  have hdiv : q ^ 2 * M' / q = q * M' := by
    rw [pow_two, mul_assoc]; exact Nat.mul_div_cancel_left (q * M') hq0
  rw [xHFunctionFieldC_eq_gamma0 κ (levelH q M') (mem_levelH_or_neg_mem q hpm M')]
  calc qExpFunctionFieldC κ (Gamma0 (q ^ 2 * M'))
      = qExpFunctionFieldC κ (Gamma0 (q ^ 2 * M' / q)) :=
        ModularCurve.qExpFunctionFieldC_gamma0_eq_qExpFunctionFieldC_gamma0_div_of_sq_dvd κ q (q ^ 2 * M')
          (dvd_mul_right _ _)
    _ = qExpFunctionFieldC κ (Gamma0 (q * M')) := by rw [hdiv]
    _ ≤ qExpFunctionFieldC κ (Gamma0 M') := qExpFunctionFieldC_gamma0_mul_le q M' hqM' κ
    _ = modularFunctionFieldC κ M' :=
        ModularCurve.qExpFunctionFieldC_gamma0_eq_modularFunctionFieldC_of_not_dvd κ M' q hqM'

theorem isSeparable_of_mem (q : ℕ) [Fact q.Prime] (hpm : ∀ u : (ZMod q)ˣ, u = 1 ∨ u = -1)
    (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (κ : Type*) [Field κ] [CharP κ q] :
    ∀ x ∈ xHFunctionFieldC κ (q ^ 2 * M') (levelH q M'), IsSeparable (↥(modularFunctionFieldC κ M')) x := by
  intro x hx
  exact isSeparable_algebraMap (⟨x, xHFunctionFieldC_levelH_le q hpm M' hqM' κ hx⟩ : ↥(modularFunctionFieldC κ M'))

theorem units_zmod_two (u : (ZMod 2)ˣ) : u = 1 ∨ u = -1 := by
  revert u; decide

theorem units_zmod_three (u : (ZMod 3)ˣ) : u = 1 ∨ u = -1 := by
  revert u; decide

end IGSEP23

end

theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (κ : Type) [Field κ] [CharP κ q] :
    ∀ x ∈ ModularCurve.xHFunctionFieldC κ (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'),
      IsSeparable (↥(ModularCurve.modularFunctionFieldC κ M')) x := by
  subst hq2
  exact IGSEP23.isSeparable_of_mem 2 IGSEP23.units_zmod_two M' hqM' κ

end S_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_isSeparable_modularFunctionFieldC_of_mem_xHFunctionFieldC_levelH_of_charP_of_eq_two (solution)
