-- Prove2me | solution 1 for HaarQuotient.exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/fa0ec4b0-ab19-5520-8e57-8c8d35abbccc

import Mathlib
import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_exists_lintegral_comp_mul_right_withDensity_density_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace HaarQuotientBochner

section Transfer

variable {G : Type*} [Group G]

@[reducible] def invariantSigma (m : MeasurableSpace G) (H : Subgroup G) : MeasurableSpace G where
  MeasurableSet' s := MeasurableSet[m] s ∧ ∀ x ∈ H, (fun g => x * g) ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, fun _ _ => rfl⟩
  measurableSet_compl s hs := ⟨hs.1.compl, fun x hx => by rw [Set.preimage_compl, hs.2 x hx]⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion fun i => (hf i).1, fun x hx => by
    rw [Set.preimage_iUnion]
    exact Set.iUnion_congr fun i => (hf i).2 x hx⟩

theorem invariantSigma_le (m : MeasurableSpace G) (H : Subgroup G) : invariantSigma m H ≤ m :=
  fun _ hs => hs.1

theorem measurableSet_invariantSigma_iff {m : MeasurableSpace G} {H : Subgroup G} {s : Set G} :
    MeasurableSet[invariantSigma m H] s ↔ MeasurableSet[m] s ∧ ∀ x ∈ H, (fun g => x * g) ⁻¹' s = s :=
  Iff.rfl

theorem measurable_invariantSigma {m : MeasurableSpace G} {H : Subgroup G} {β : Type*} [MeasurableSpace β]
    {Φ : G → β} (hΦ : Measurable[m] Φ) (hΦH : ∀ x ∈ H, ∀ g : G, Φ (x * g) = Φ g) :
    Measurable[invariantSigma m H] Φ := by
  intro t ht
  refine ⟨hΦ ht, fun x hx => ?_⟩
  ext g
  simp only [Set.mem_preimage, hΦH x hx g]

theorem trim_eq_trim_of_forall_lintegral_eq {m : MeasurableSpace G} (H : Subgroup G) (μ ν : Measure G)
    (hμν : ∀ f : G → ℝ≥0∞, Measurable f → (∀ x ∈ H, ∀ g : G, f (x * g) = f g) → ∫⁻ g, f g ∂μ = ∫⁻ g, f g ∂ν) :
    μ.trim (invariantSigma_le m H) = ν.trim (invariantSigma_le m H) := by
  refine @Measure.ext _ (invariantSigma m H) _ _ fun s hs => ?_
  rw [trim_measurableSet_eq _ hs, trim_measurableSet_eq _ hs]
  obtain ⟨hsm, hsH⟩ := hs
  have hind : ∀ x ∈ H, ∀ g : G, s.indicator (fun _ => (1 : ℝ≥0∞)) (x * g) = s.indicator (fun _ => (1 : ℝ≥0∞)) g := by
    intro x hx g
    have hmem : x * g ∈ s ↔ g ∈ s := by
      constructor
      · intro h
        have : g ∈ (fun g => x * g) ⁻¹' s := h
        rwa [hsH x hx] at this
      · intro h
        have : g ∈ (fun g => x * g) ⁻¹' s := by rwa [hsH x hx]
        exact this
    by_cases hg : g ∈ s
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.mpr hg)]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.mp h))]
  have := hμν (s.indicator fun _ => 1) (measurable_const.indicator hsm) hind
  rwa [lintegral_indicator_const hsm, lintegral_indicator_const hsm, one_mul, one_mul] at this

theorem integral_eq_of_forall_lintegral_eq {m : MeasurableSpace G} (H : Subgroup G) (μ ν : Measure G)
    (hμν : ∀ f : G → ℝ≥0∞, Measurable f → (∀ x ∈ H, ∀ g : G, f (x * g) = f g) → ∫⁻ g, f g ∂μ = ∫⁻ g, f g ∂ν)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (Φ : G → E) (hΦ : Measurable Φ) (hΦH : ∀ x ∈ H, ∀ g : G, Φ (x * g) = Φ g) :
    ∫ g, Φ g ∂μ = ∫ g, Φ g ∂ν := by
  have hle := invariantSigma_le m H
  have hsm : StronglyMeasurable[invariantSigma m H] Φ :=
    @Measurable.stronglyMeasurable _ _ _ (invariantSigma m H) _ _ _ _ _ (measurable_invariantSigma hΦ hΦH)
  rw [integral_trim hle hsm, integral_trim hle hsm, trim_eq_trim_of_forall_lintegral_eq H μ ν hμν]

omit [Group G] in

theorem integrable_of_lintegral_enorm_eq {m : MeasurableSpace G} (μ ν : Measure G)
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Φ : G → E) (hΦ : Measurable Φ) (h : ∫⁻ g, ‖Φ g‖ₑ ∂ν = ∫⁻ g, ‖Φ g‖ₑ ∂μ) (hint : Integrable Φ μ) :
    Integrable Φ ν := by
  refine ⟨hΦ.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, h]
  exact hint.2

end Transfer

end HaarQuotientBochner

end

open MeasureTheory HaarQuotientBochner
open scoped NNReal ENNReal Pointwise

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (μ : Measure G) [μ.IsHaarMeasure]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant] (x : G) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ (Φ : G → E), Measurable Φ → (∀ (h : H) (g : G), Φ ((h : G) * g) = Φ g) →
      (Integrable (fun g => Φ (g * x)) (μ.withDensity (HaarQuotient.density H μH)) ↔
        Integrable Φ (μ.withDensity (HaarQuotient.density H μH))) ∧
      (∫ g, Φ (g * x) ∂(μ.withDensity (HaarQuotient.density H μH))) =
        (c : ℝ) • ∫ g, Φ g ∂(μ.withDensity (HaarQuotient.density H μH)) := by
  obtain ⟨c, hc0, hc⟩ := HaarQuotient.exists_lintegral_comp_mul_right_withDensity_density_eq_mul μ H hH μH x

  obtain ⟨c', hc'0, hc'⟩ := HaarQuotient.exists_lintegral_comp_mul_right_withDensity_density_eq_mul μ H hH μH x⁻¹
  set ν : Measure G := μ.withDensity (HaarQuotient.density H μH) with hν
  refine ⟨c, hc0, fun Φ hΦ hΦH => ?_⟩
  have hΦH' : ∀ y ∈ H, ∀ g : G, Φ (y * g) = Φ g := fun y hy g => hΦH ⟨y, hy⟩ g
  have hΦx : Measurable fun g => Φ (g * x) := hΦ.comp (measurable_mul_const x)

  have hnorm : ∫⁻ g, ‖Φ (g * x)‖ₑ ∂ν = c * ∫⁻ g, ‖Φ g‖ₑ ∂ν :=
    hc (fun g => ‖Φ g‖ₑ) hΦ.enorm fun h g => by simp only [hΦH h g]
  have hnorm' : ∫⁻ g, ‖Φ g‖ₑ ∂ν = c' * ∫⁻ g, ‖Φ (g * x)‖ₑ ∂ν := by
    have := hc' (fun g => ‖Φ (g * x)‖ₑ) hΦx.enorm fun h g => by simp only [mul_assoc, hΦH h (g * x)]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using this
  have hint : Integrable (fun g => Φ (g * x)) ν ↔ Integrable Φ ν := by
    constructor
    · intro hI
      refine ⟨hΦ.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral, hnorm']
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top hI.2
    · intro hI
      refine ⟨hΦx.aestronglyMeasurable, ?_⟩
      rw [HasFiniteIntegral, hnorm]
      exact ENNReal.mul_lt_top ENNReal.coe_lt_top hI.2
  refine ⟨hint, ?_⟩

  set e : G ≃ᵐ G := MeasurableEquiv.mulRight x with he
  have hex : ∀ g : G, e g = g * x := fun g => rfl
  have h1 : ∫ g, Φ (g * x) ∂ν = ∫ g, Φ g ∂(Measure.map e ν) := by
    rw [integral_map_equiv]
    simp only [hex]
  have hagree : ∀ f : G → ℝ≥0∞, Measurable f → (∀ y ∈ H, ∀ g : G, f (y * g) = f g) →
      ∫⁻ g, f g ∂(Measure.map e ν) = ∫⁻ g, f g ∂((c : ℝ≥0∞) • ν) := by
    intro f hf hfH
    rw [lintegral_map_equiv, lintegral_smul_measure]
    exact hc f hf fun h g => hfH h h.2 g
  rw [h1, integral_eq_of_forall_lintegral_eq H _ _ hagree Φ hΦ hΦH', integral_smul_measure, ENNReal.coe_toReal]

end S_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul
end P2MW
export P2MW.S_HaarQuotient_exists_forall_integrable_comp_mul_right_iff_and_integral_eq_smul (solution)
