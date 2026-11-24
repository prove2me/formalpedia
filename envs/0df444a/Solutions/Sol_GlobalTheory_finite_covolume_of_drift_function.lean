-- Prove2me | solution 1 for GlobalTheory.finite_covolume_of_drift_function
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:48:56.535398+00:00
-- url     : https://prove2.me/submissions/9820f8ce-540c-4d9c-98bc-a3f34e9f64c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_FiniteCovolumeOfDriftFunction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y) (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) → (∀ s y y', R y y' → R (t s y) (t s y')) → (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') → ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) → Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b → (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) → ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → Countable Γ ∧ ∃ F : Set G, MeasurableSet F ∧ ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (h k : G), k * h = h⁻¹ * k → ν.map (fun g => g * h) = ν) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) [Countable Γ] (F : Set G), MeasurableSet F → (∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ F) → (∀ h : G, ν.map (fun g => g * h) = ν → ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) → ∫⁻ g in F, φ (g * h) ∂ν = ∫⁻ g in F, φ g ∂ν) ∧ ∀ K : Set G, MeasurableSet K → ν (F ∩ {g | ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k}) ≤ ν K) → (∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] (Γ : Subgroup G) (σ : Type) [Fintype σ] [Nonempty σ] (h : σ → G) (f : G → ℝ) (c b : ℝ), (∃ U ∈ 𝓝 (1 : G), ∀ γ ∈ Γ, γ ∈ U → γ = 1) → (∀ s, ∃ k : G, k * h s = (h s)⁻¹ * k) → Measurable f → (∀ g, 0 ≤ f g) → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → 0 ≤ c → c < 1 → 0 ≤ b → (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) → (∀ M : ℝ, ∃ K : Set G, IsCompact K ∧ ∀ g, f g ≤ M → ∃ γ ∈ Γ, ∃ k ∈ K, g = γ * k) → ∃ Ω : Set G, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : G, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w) := by
  intro h₁ h₂ h₃ h₄ G _ _ _ _ _ _ _ _ ν _ Γ σ _ _ h f c b hΓ hh hf hf0 hfΓ hc0 hc1 hb hd hK
  obtain ⟨hcount, F, hF, hFu⟩ := h₂ G Γ hΓ
  obtain ⟨hinv, hle⟩ := h₄ G ν Γ F hF hFu
  obtain ⟨M, hM⟩ := h₁ G σ (ν.restrict F) (fun y y' => ∃ γ ∈ Γ, y' = γ * y)
    (fun s g => g * h s) f c b (fun s => measurable_mul_const (h s))
    (by
      rintro s y y' ⟨γ, hγ, rfl⟩
      exact ⟨γ, hγ, mul_assoc _ _ _⟩)
    (by
      intro φ hφ hR s
      obtain ⟨k, hk⟩ := hh s
      exact hinv (h s) (h₃ G ν (h s) k hk) φ hφ
        (fun γ hγ g => (hR g (γ * g) ⟨γ, hγ, rfl⟩).symm))
    hf hf0
    (by
      rintro y y' ⟨γ, hγ, rfl⟩
      exact (hfΓ γ hγ y).symm)
    hc0 hc1 hb hd
  obtain ⟨K, hKc, hKf⟩ := hK M
  refine ⟨F, hF, ?_, ?_⟩
  · rw [Measure.restrict_apply_univ, Measure.restrict_apply' hF] at hM
    have h5 : ν ({y | f y ≤ M} ∩ F) ≤ ν K := by
      refine le_trans (measure_mono ?_) (hle K hKc.measurableSet)
      rintro g ⟨hg, hgF⟩
      exact ⟨hgF, hKf g hg⟩
    refine lt_of_le_of_lt hM (ENNReal.mul_lt_top (by simp) ?_)
    exact lt_of_le_of_lt h5 hKc.measure_lt_top
  · intro g
    obtain ⟨γ, hγ, -⟩ := hFu g
    exact ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, γ * g, hγ, by group⟩
end GlobalTheory
