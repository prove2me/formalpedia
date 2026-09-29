-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.smul_mem_integers_and_residue_ne_zero_iff_valuation_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/1bcd350e-f4ad-5ecd-ac98-5f37b7c694f1

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_smul_mem_integers_and_residue_ne_zero_iff_valuation_eq
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

namespace ScalVal

theorem isUnit_mk_iff {F : Type*} [Field F] (O : ValuationSubring F) (g : F) (hg : g ∈ O) :
    IsUnit (⟨g, hg⟩ : O) ↔ g ≠ 0 ∧ g⁻¹ ∈ O := by
  constructor
  · rintro ⟨u, hu⟩
    have hmul : g * ((u⁻¹ : Oˣ) : O).1 = 1 := by
      have := congrArg (fun w : O => (w : F)) u.mul_inv
      simpa [hu] using this
    have hg0 : g ≠ 0 := fun h => by simp [h] at hmul
    refine ⟨hg0, ?_⟩
    have : g⁻¹ = ((u⁻¹ : Oˣ) : O).1 := by rw [inv_eq_of_mul_eq_one_right hmul]
    rw [this]; exact ((u⁻¹ : Oˣ) : O).2
  · rintro ⟨hg0, hinv⟩
    exact ⟨⟨⟨g, hg⟩, ⟨g⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hg0), Subtype.ext (inv_mul_cancel₀ hg0)⟩, rfl⟩

theorem unit_smul_iff {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar] (R : RegularProlongation A F Fbar)
    (f : F) (c₀ : L) (h₀ : c₀ • f ∈ R.integers) (hr₀ : R.residue ⟨c₀ • f, h₀⟩ ≠ 0) (c' : L) :
    (∃ h : c' • f ∈ R.integers, R.residue ⟨c' • f, h⟩ ≠ 0) ↔ A.valuation c' = A.valuation c₀ := by
  have hc₀ : c₀ ≠ 0 := R.smul_const_ne_zero h₀ hr₀
  have hu₀ : IsUnit (⟨c₀ • f, h₀⟩ : R.integers) := R.isUnit_of_residue_ne_zero hr₀
  obtain ⟨hg0, hginv⟩ := (isUnit_mk_iff R.integers _ h₀).mp hu₀
  have hsmul : ∀ c : L, c • f = algebraMap L F (c / c₀) * (c₀ • f) := fun c => by
    rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul, div_mul_cancel₀ _ hc₀]
  have hv₀ : 0 < A.valuation c₀ := (Valuation.pos_iff _).mpr hc₀

  rcases eq_or_ne c' 0 with rfl | hc'
  · constructor
    · rintro ⟨h', hr'⟩
      exfalso; apply hr'
      have : (⟨(0 : L) • f, h'⟩ : R.integers) = 0 := Subtype.ext (by simp)
      rw [this, map_zero]
    · intro h
      rw [map_zero] at h
      exact absurd h.symm hv₀.ne'
  have hv' : 0 < A.valuation c' := (Valuation.pos_iff _).mpr hc'

  have hratio : (c' / c₀ ∈ A ∧ c₀ / c' ∈ A) ↔ A.valuation c' = A.valuation c₀ := by
    rw [← A.valuation_le_one_iff, ← A.valuation_le_one_iff, map_div₀, map_div₀, div_le_one₀ hv₀, div_le_one₀ hv']
    exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  rw [← hratio]
  constructor
  · rintro ⟨h', hr'⟩
    have hu' : IsUnit (⟨c' • f, h'⟩ : R.integers) := R.isUnit_of_residue_ne_zero hr'
    obtain ⟨hg0', hginv'⟩ := (isUnit_mk_iff R.integers _ h').mp hu'
    have ht : algebraMap L F (c' / c₀) = (c' • f) * (c₀ • f)⁻¹ := by
      rw [hsmul c', mul_assoc, mul_inv_cancel₀ hg0, mul_one]
    have ht' : algebraMap L F (c₀ / c') = (c₀ • f) * (c' • f)⁻¹ := by
      rw [← inv_div, map_inv₀, ht, mul_inv, inv_inv, mul_comm]
    refine ⟨(R.algebraMap_mem_iff _).mp ?_, (R.algebraMap_mem_iff _).mp ?_⟩
    · rw [ht]; exact mul_mem h' hginv
    · rw [ht']; exact mul_mem h₀ hginv'
  · rintro ⟨h1, h2⟩
    have ht₁ : algebraMap L F (c' / c₀) ∈ R.integers := (R.algebraMap_mem_iff _).mpr h1
    have ht₂ : algebraMap L F (c₀ / c') ∈ R.integers := (R.algebraMap_mem_iff _).mpr h2
    have hmem : c' • f ∈ R.integers := by rw [hsmul c']; exact mul_mem ht₁ h₀
    refine ⟨hmem, R.residue_ne_zero_of_isUnit ?_⟩
    rw [isUnit_mk_iff]
    refine ⟨by rw [hsmul c']; exact mul_ne_zero (by rw [map_ne_zero]; exact div_ne_zero hc' hc₀) hg0, ?_⟩
    rw [hsmul c', mul_inv, ← map_inv₀, inv_div]
    exact mul_mem ht₂ hginv

end ScalVal

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    {P : PlaceSpecialization A q N data hKr k red hα hβ}
    (R : ProlongationTuple P) (hR : R.IsModel)
    (f : ↥(modularFunctionFieldBar (N * q))) (hf0 : f ≠ 0)
    (c₀ : AlgebraicClosure ℚ) (h₀ : c₀ • f ∈ R.R₁.integers) (hr₀ : R.R₁.residue ⟨c₀ • f, h₀⟩ ≠ 0)
    (c' : AlgebraicClosure ℚ) :
    ((∃ h : c' • f ∈ R.R₁.integers, R.R₁.residue ⟨c' • f, h⟩ ≠ 0) ↔ A.valuation c' = A.valuation c₀) ∧
    (∀ (d₀ : AlgebraicClosure ℚ) (hd₀ : d₀ • f ∈ R.R₂.integers), R.R₂.residue ⟨d₀ • f, hd₀⟩ ≠ 0 →
      ∀ d' : AlgebraicClosure ℚ,
        ((∃ h : d' • f ∈ R.R₂.integers, R.R₂.residue ⟨d' • f, h⟩ ≠ 0) ↔ A.valuation d' = A.valuation d₀)) := by
  exact ⟨ScalVal.unit_smul_iff R.R₁ (f : ↥(modularFunctionFieldBar (N * q))) c₀ h₀ hr₀ c',
    fun d₀ hd₀ hrd₀ d' => ScalVal.unit_smul_iff R.R₂ (f : ↥(modularFunctionFieldBar (N * q))) d₀ hd₀ hrd₀ d'⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_smul_mem_integers_and_residue_ne_zero_iff_valuation_eq
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_smul_mem_integers_and_residue_ne_zero_iff_valuation_eq (solution)
