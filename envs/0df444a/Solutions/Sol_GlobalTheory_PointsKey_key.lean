-- Prove2me | solution 1 for GlobalTheory.PointsKey.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:14:23.538442+00:00
-- url     : https://prove2.me/submissions/8006b00b-9ff4-4ef9-b550-c18f22d2348f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FrobeniusPowEquationDvdAllPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PowDvdOfVanishingAtPerfectValuationPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdAllPowOfFrobeniusEqKilledByPerfectPoints
import Theorems.Thm_GlobalTheory_PointsKey_dvd_of_one_sub_mul
import Theorems.Thm_GlobalTheory_T_frobeniusPowEquation_dvd_all_pow
import Theorems.Thm_GlobalTheory_T_pow_dvd_of_vanishing_at_perfect_valuation_points


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
open GlobalTheory GlobalTheory.PointsKey
namespace GlobalTheory.PointsKey
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → ∀ j, f (D j) = 0) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h heq hpts m j
  set S := oneSubMul u with hS
  let R' := Localization S
  let φ : R →+* R' := algebraMap R R'
  have hl' : ((l : ℕ) : R') = 0 := by rw [← map_natCast φ, hl, map_zero]
  have hu' : φ u ∈ nonZeroDivisors R' := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    have hx' : φ u * IsLocalization.mk' R' a s = 0 := by rw [mul_comm]; exact hx
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx'
    obtain ⟨t, ht⟩ := hx'
    have hta : (t : R) * a = 0 := by
      rw [mem_nonZeroDivisors_iff_right] at hu
      exact hu _ (by rw [← ht]; ring)
    exact (IsLocalization.mk'_eq_zero_iff a s).2 ⟨t, hta⟩
  have hunit : ∀ r', IsUnit (1 - φ u * r') := by
    intro r'
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S r'
    obtain ⟨b, hb⟩ := s.2
    have hmem : (s : R) - u * a ∈ S := ⟨b + a, by rw [hb]; ring⟩
    have hsp := IsLocalization.mk'_spec R' a s
    have : (1 - φ u * IsLocalization.mk' R' a s) * φ s = φ ((s : R) - u * a) := by
      rw [map_sub, map_mul, sub_mul, one_mul, mul_assoc, hsp]
    exact isUnit_of_mul_isUnit_left (this ▸ IsLocalization.map_units R' ⟨_, hmem⟩)
  have heq' : ∀ j, φ u ^ h * φ (D j) = ∑ i, φ (D i) ^ l * φ (c i j) := by
    intro j; simpa [map_sum, map_mul, map_pow] using congrArg φ (heq j)
  have hpts' : ∀ j, ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R' →+* O), f (φ u) ≠ 0 → ¬ IsUnit (f (φ u)) → IsAdicComplete (Ideal.span {f (φ u)}) O → f (φ (D j)) = 0 := by
    intro j O _ _ _ _ _ f h1 h2 h3
    exact hpts O (f.comp φ) h1 h2 h3 j
  have hb : ∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, φ u ^ (M * n) ∣ φ u ^ c * φ (D j) ^ n := fun j M =>
    GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points l R' (φ u) (φ (D j)) hl' hu' hunit (hpts' j) M
  obtain ⟨y, hy⟩ := GlobalTheory.T.frobeniusPowEquation_dvd_all_pow l R' (φ u) hl' hu' κ (fun i => φ (D i)) (fun i j => φ (c i j)) h heq' hb m j
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S y
  have h2 : φ (D j * s) = φ (u ^ m * a) := by
    rw [map_mul, hy, map_mul, map_pow, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists S R').1 h2
  obtain ⟨r, hr⟩ := (t * s).2
  refine dvd_of_one_sub_mul u r (D j) (t * a) m ?_
  rw [← hr]
  simp only [Submonoid.coe_mul]
  linear_combination ht
end GlobalTheory.PointsKey
