-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/84420d9b-0df8-5fc1-8139-a85a22570040

import Mathlib
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

section AddOneHelpers

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem place_ord_neg_one : v.ord (-1 : F) = 0 := by
  have h := v.ord_inv (-1 : F)
  rw [inv_neg, inv_one] at h
  omega

private theorem place_ord_add_one_of_neg {x : F} (hx : v.ord x < 0) : v.ord (x + 1) < 0 := by
  by_contra hcon
  have hx1 : x + 1 ≠ 0 := by
    intro h0
    have hx' : x = -1 := eq_neg_of_add_eq_zero_left h0
    rw [hx', place_ord_neg_one] at hx
    exact lt_irrefl _ hx
  have hmem : x + 1 ∈ v.toValuationSubring := v.mem_of_ord_nonneg hx1 (not_lt.mp hcon)
  have hxmem : x ∈ v.toValuationSubring := by
    have h := sub_mem hmem (one_mem v.toValuationSubring)
    rwa [add_sub_cancel_right] at h
  exact absurd (v.ord_nonneg_of_mem hxmem) (not_le.mpr hx)

private theorem place_ord_add_one_of_zero_or_pos {y : F} (hy : y = 0 ∨ 0 < v.ord y) :
    y + 1 ≠ 0 ∧ v.ord (y + 1) ≤ 0 := by
  rcases hy with rfl | hy
  · simp
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hy
  have hy1 : y + 1 ≠ 0 := by
    intro h0
    have hy' : y = -1 := eq_neg_of_add_eq_zero_left h0
    rw [hy', place_ord_neg_one] at hy
    exact lt_irrefl _ hy
  refine ⟨hy1, ?_⟩
  by_contra hcon
  have hz : 0 < v.ord (y + 1) := not_le.mp hcon
  have hmemy : y ∈ v.toValuationSubring := v.mem_of_ord_nonneg hy0 hy.le
  have hmemz : y + 1 ∈ v.toValuationSubring := v.mem_of_ord_nonneg hy1 hz.le
  have hz' := v.mk_mem_maximalIdeal_of_ord_pos hmemz hz
  have hy' := v.mk_mem_maximalIdeal_of_ord_pos hmemy hy
  have hone : (1 : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    have h := Ideal.sub_mem _ hz' hy'
    convert h using 1
    ext
    simp
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top hone

private theorem place_ord_add_one_of_nonneg {x : F} (hx : 0 ≤ v.ord x) : 0 ≤ v.ord (x + 1) := by
  have hxmem : x ∈ v.toValuationSubring := by
    rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_mem _
    · exact v.mem_of_ord_nonneg hx0 hx
  exact v.ord_nonneg_of_mem (add_mem hxmem (one_mem _))

end AddOneHelpers

theorem solution
    {N : ℕ} [NeZero N] {q : ℕ} [Fact q.Prime] (hqN : ¬ q ∣ N)
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] [DecidableEq k] [IsAlgClosed k]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))]
    {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P) (hR : R.IsModel) (hO : R.OrderLawFixed)
    (f : modularFunctionFieldBar (N * q)) (h₁ : f ∈ R.R₁.integers) (h₂ : f ∈ R.R₂.integers)
    (v : Place k (modularFunctionFieldC k N))
    (hfix : frobOnPlacesGeomLevel k N data hKr (frobOnPlacesGeomLevel k N data hKr v) = v)
    (haff : IsAffineGeomPlace k N v)
    (hpole : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst V = v → 0 ≤ V.ord f) :
    (R.residue₁ ⟨f, h₁⟩ ≠ 0 → 0 ≤ v.ord (R.residue₁ ⟨f, h₁⟩)) ∧
    (R.residue₂ ⟨f, h₂⟩ ≠ 0 → 0 ≤ (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)) := by
  have _ := hqN
  have _ := hR

  have ne_of_ne₁ : ∀ (g : modularFunctionFieldBar (N * q)) (hg : g ∈ R.R₁.integers),
      R.residue₁ ⟨g, hg⟩ ≠ 0 → R.R₁.residue ⟨g, hg⟩ ≠ 0 := by
    intro g hg h h0
    apply h
    rw [ProlongationTuple.residue₁_apply, h0, map_zero]
  have ne_of_ne₂ : ∀ (g : modularFunctionFieldBar (N * q)) (hg : g ∈ R.R₂.integers),
      R.residue₂ ⟨g, hg⟩ ≠ 0 → R.R₂.residue ⟨g, hg⟩ ≠ 0 := by
    intro g hg h h0
    apply h
    rw [ProlongationTuple.residue₂_apply, h0, map_zero]

  have core : ∀ (g : modularFunctionFieldBar (N * q)) (hg₁ : g ∈ R.R₁.integers)
      (hg₂ : g ∈ R.R₂.integers), R.residue₁ ⟨g, hg₁⟩ ≠ 0 → R.residue₂ ⟨g, hg₂⟩ ≠ 0 →
      (∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        P.reduceFst V = v → 0 ≤ V.ord g) →
      0 ≤ v.ord (R.residue₁ ⟨g, hg₁⟩) + (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨g, hg₂⟩) := by
    intro g hg₁ hg₂ hn₁ hn₂ hg
    classical
    have hg0 : g ≠ 0 := by
      rintro rfl
      apply hn₁
      have h0 : (⟨0, hg₁⟩ : R.R₁.integers) = 0 := rfl
      rw [h0, map_zero]
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := AlgebraicClosure ℚ) g hg0
    have hsum := hO g hg₁ hg₂ (ne_of_ne₁ g hg₁ hn₁) (ne_of_ne₂ g hg₂ hn₂) D hD v hfix haff
    rw [← hsum, Finsupp.mapDomain, Finsupp.sum_apply]
    unfold Finsupp.sum
    apply Finset.sum_nonneg
    intro V _
    simp only [Finsupp.single_apply]
    split_ifs with hV
    · rw [hD]
      exact hg V hV
    · exact le_rfl

  have hf₁' : f + 1 ∈ R.R₁.integers := add_mem h₁ (one_mem _)
  have hf₂' : f + 1 ∈ R.R₂.integers := add_mem h₂ (one_mem _)
  have hres₁' : R.residue₁ ⟨f + 1, hf₁'⟩ = R.residue₁ ⟨f, h₁⟩ + 1 := by
    have h : (⟨f + 1, hf₁'⟩ : R.R₁.integers) = ⟨f, h₁⟩ + 1 := rfl
    rw [h, map_add, map_one]
  have hres₂' : R.residue₂ ⟨f + 1, hf₂'⟩ = R.residue₂ ⟨f, h₂⟩ + 1 := by
    have h : (⟨f + 1, hf₂'⟩ : R.R₂.integers) = ⟨f, h₂⟩ + 1 := rfl
    rw [h, map_add, map_one]
  have hpole' : ∀ V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      P.reduceFst V = v → 0 ≤ V.ord (f + 1) :=
    fun V hV => place_ord_add_one_of_nonneg V (hpole V hV)
  refine ⟨?_, ?_⟩
  ·
    intro hn₁
    by_contra hcon
    have hx : v.ord (R.residue₁ ⟨f, h₁⟩) < 0 := not_le.mp hcon
    by_cases hy : R.residue₂ ⟨f, h₂⟩ = 0 ∨ 0 < (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩)
    · obtain ⟨hy1, hy2⟩ := place_ord_add_one_of_zero_or_pos (frobOnPlacesGeomLevel k N data hKr v) hy
      have hx' := place_ord_add_one_of_neg v hx
      have hx1 : R.residue₁ ⟨f, h₁⟩ + 1 ≠ 0 := by
        intro h0
        rw [h0, Place.ord_zero] at hx'
        exact lt_irrefl _ hx'
      have h := core (f + 1) hf₁' hf₂' (by rwa [hres₁']) (by rwa [hres₂']) hpole'
      rw [hres₁', hres₂'] at h
      omega
    · push Not at hy
      have h := core f h₁ h₂ hn₁ hy.1 hpole
      have hy2 := hy.2
      omega
  ·
    intro hn₂
    by_contra hcon
    have hy : (frobOnPlacesGeomLevel k N data hKr v).ord (R.residue₂ ⟨f, h₂⟩) < 0 := not_le.mp hcon
    by_cases hx : R.residue₁ ⟨f, h₁⟩ = 0 ∨ 0 < v.ord (R.residue₁ ⟨f, h₁⟩)
    · obtain ⟨hx1, hx2⟩ := place_ord_add_one_of_zero_or_pos v hx
      have hy' := place_ord_add_one_of_neg (frobOnPlacesGeomLevel k N data hKr v) hy
      have hy1 : R.residue₂ ⟨f, h₂⟩ + 1 ≠ 0 := by
        intro h0
        rw [h0, Place.ord_zero] at hy'
        exact lt_irrefl _ hy'
      have h := core (f + 1) hf₁' hf₂' (by rwa [hres₁']) (by rwa [hres₂']) hpole'
      rw [hres₁', hres₂'] at h
      omega
    · push Not at hx
      have h := core f h₁ h₂ hx.1 hn₂ hpole
      have hx2 := hx.2
      omega

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residues_nonneg_of_forall_reduceFst_eq_ord_nonneg (solution)
