-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/057e2fca-e209-5376-81e6-c55e0010f346

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap
import Theorems.Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
import Theorems.Thm_AlgebraicCurve_RegularProlongation_krullDimLE_one_integers
import Theorems.Thm_ValuationSubring_krullDimLE_one_of_isAlgebraic_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss
p2m_attr_erase "simp" "ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rpd.R₁.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by

  have hGM := ModularCurve.JHPlaceSpecialization.exists_regularProlongation_mem_integers_iff_gauss_and_residue_coeffMap p M H hpM hpM2 hHp A hA
  obtain ⟨G, hg, hresG⟩ := hGM

  have hle : G.integers ≤ Rpd.R₁.integers := by
    intro f hf
    obtain ⟨x₀, y₀, hy₀, hxy₀⟩ := (hg f).mp hf
    obtain ⟨x, y, hx, hy, hybar, hxy'⟩ := ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq p M H hpM hpM2 A hA f x₀ y₀ hy₀ hxy₀
    have hxy : f * ⟨coeffMap A.subtype y, hy⟩ = (⟨coeffMap A.subtype x, hx⟩ : ↥(xHFunctionFieldBar M H)) := Subtype.ext hxy'
    obtain ⟨hyint, hyres⟩ := Rpd.residue₁_coeffMap y hy
    obtain ⟨hxint, -⟩ := Rpd.residue₁_coeffMap x hx

    have hres_ne : Rpd.R₁.residue ⟨_, hyint⟩ ≠ 0 := by
      intro h0
      apply hybar
      have := congrArg (fun g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A) => ((g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A))) h0
      simp only [ZeroMemClass.coe_zero] at this
      rw [← hyres]; exact this
    have hunit : IsUnit (⟨_, hyint⟩ : ↥Rpd.R₁.integers) := Rpd.R₁.isUnit_of_residue_ne_zero hres_ne
    obtain ⟨u, hu⟩ := hunit
    have hy0 : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ≠ 0 := by
      intro h0
      apply hres_ne
      have : (⟨_, hyint⟩ : ↥Rpd.R₁.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]

    have hv : Rpd.R₁.integers.valuation (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) = 1 := by
      have := Rpd.R₁.integers.valuation_unit u
      rw [hu] at this
      exact this
    have hfeq : f = ⟨coeffMap A.subtype x, hx⟩ * (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H))⁻¹ := by
      rw [← hxy, mul_inv_cancel_right₀ hy0]
    rw [← Rpd.R₁.integers.valuation_le_one_iff, hfeq, map_mul, map_inv₀, hv, inv_one, mul_one]
    exact (Rpd.R₁.integers.valuation_le_one_iff _).mpr hxint

  haveI : Ring.KrullDimLE 1 ↥A := ValuationSubring.krullDimLE_one_of_isAlgebraic_rat A
  haveI : Ring.KrullDimLE 1 ↥G.integers := AlgebraicCurve.RegularProlongation.krullDimLE_one_integers A G
  rcases ValuationSubring.eq_self_or_eq_top_of_le hle with h | h
  · intro f
    rw [← h]
    exact hg f
  ·
    exfalso
    have hmem : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((p : AlgebraicClosure ℚ)⁻¹) ∈ Rpd.R₁.integers := by
      rw [h]; trivial
    have hA' : ((p : AlgebraicClosure ℚ)⁻¹) ∈ A := (Rpd.R₁.algebraMap_mem_iff _).mp hmem
    have hnu : (p : AlgebraicClosure ℚ) ∈ A.nonunits := hA
    rcases (ValuationSubring.mem_nonunits_iff_or A).mp hnu with h0 | hinv
    · exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h0
    · exact hinv hA'

end S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss (solution)
