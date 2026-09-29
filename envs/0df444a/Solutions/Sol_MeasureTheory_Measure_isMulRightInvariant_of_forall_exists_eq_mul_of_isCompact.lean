-- Prove2me | solution 1 for MeasureTheory.Measure.isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b388b7ad-1dea-5a3d-bc83-23fc8476f55a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G] [T2Space G]
    (Z C : Set G) (hZ : ∀ z ∈ Z, ∀ g : G, g * z = z * g)
    (hC : IsCompact C) (hcov : ∀ g : G, ∃ z ∈ Z, ∃ k ∈ C, g = z * k)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by

  set Δ : G →* ℝ≥0 := Measure.modularCharacter with hΔ_def
  have hΔ : ∀ g : G, Δ g = Measure.haarScalarFactor (Measure.map (· * g) μ) μ := fun g =>
    Measure.modularCharacterFun_eq_haarScalarFactor μ g
  have hmap : ∀ g : G, Measure.map (· * g) μ = Δ g • μ := fun g => by
    rw [hΔ]
    exact Measure.isMulLeftInvariant_eq_smul _ _

  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts G) := inferInstance
  have hm0 : 0 < μ (K₀ : Set G) :=
    (isOpen_interior.measure_pos μ K₀.interior_nonempty).trans_le (measure_mono interior_subset)
  have hmtop : μ (K₀ : Set G) < ⊤ := K₀.isCompact.measure_lt_top

  have hZ1 : ∀ z ∈ Z, Δ z = 1 := by
    intro z hz
    have h : Measure.map (· * z) μ = μ := by
      have hfun : (fun x : G => x * z) = fun x => z * x := funext fun x => hZ z hz x
      rw [hfun]
      exact map_mul_left_eq_self μ z
    have h2 := hmap z
    rw [h] at h2
    have h3 := congrArg (fun ν : Measure G => ν (K₀ : Set G)) h2
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    rw [← one_mul (μ (K₀ : Set G))] at h3
    conv_rhs at h3 => rw [one_mul]
    have h4 : (1 : ℝ≥0∞) = (Δ z : ℝ≥0∞) := (ENNReal.mul_left_inj hm0.ne' hmtop.ne).1 h3
    exact (ENNReal.coe_eq_one.1 h4.symm)
  set B : ℝ≥0∞ := μ ((fun p : G × G => p.1 * p.2⁻¹) '' ((K₀ : Set G) ×ˢ C)) with hB_def
  have hBtop : B < ⊤ :=
    ((K₀.isCompact.prod hC).image (by fun_prop)).measure_lt_top
  have hbound : ∀ g : G, (Δ g : ℝ≥0∞) * μ (K₀ : Set G) ≤ B := by
    intro g
    obtain ⟨z, hz, k, hk, rfl⟩ := hcov g
    rw [map_mul, hZ1 z hz, one_mul]
    have h1 : Measure.map (· * k) μ (K₀ : Set G) = (Δ k : ℝ≥0∞) * μ (K₀ : Set G) := by
      rw [hmap k, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [← h1, Measure.map_apply (measurable_mul_const k) K₀.isCompact.measurableSet]
    refine measure_mono fun x hx => ?_
    exact ⟨(x * k, k), ⟨hx, hk⟩, by simp⟩
  have hle : ∀ g : G, Δ g ≤ (B / μ (K₀ : Set G)).toNNReal := by
    intro g
    have h : (Δ g : ℝ≥0∞) ≤ B / μ (K₀ : Set G) := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hm0.ne') (Or.inl hmtop.ne)]
      exact hbound g
    rwa [← ENNReal.coe_toNNReal (ENNReal.div_lt_top hBtop.ne hm0.ne').ne, ENNReal.coe_le_coe] at h

  have hone : ∀ g : G, Δ g = 1 := by
    by_contra hne
    obtain ⟨g, hg⟩ := not_forall.1 hne
    obtain ⟨h, hh⟩ : ∃ h : G, 1 < Δ h := by
      rcases lt_or_gt_of_ne hg with hlt | hgt
      · refine ⟨g⁻¹, ?_⟩
        have hinv : Δ g⁻¹ = (Δ g)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← map_mul, inv_mul_cancel, map_one])
        have hpos : 0 < Δ g := Measure.modularCharacterFun_pos g
        rw [hinv]
        exact (one_lt_inv₀ hpos).2 hlt
      · exact ⟨g, hgt⟩
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((B / μ (K₀ : Set G)).toNNReal) hh
    have := hle (h ^ n)
    rw [map_pow] at this
    exact absurd (lt_of_lt_of_le hn this) (lt_irrefl _)
  exact ⟨fun g => by rw [hmap g, hone g, one_smul]⟩

end S_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact
end P2MW
export P2MW.S_MeasureTheory_Measure_isMulRightInvariant_of_forall_exists_eq_mul_of_isCompact (solution)
