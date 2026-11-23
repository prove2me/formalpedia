-- Prove2me | solution 1 for GlobalTheory.integrableOn_fundamentalDomain_of_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:54:08.129676+00:00
-- url     : https://prove2.me/submissions/09febfcf-99fb-4eab-a112-e6e99870dec2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IntegrableOnFundamentalDomainOfCocompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory
open GlobalTheory
open Pointwise
namespace GlobalTheory
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (K : Set G), IsCompact K → (∀ g : G, ∃ γ ∈ Γ, γ * g ∈ K) → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ (f : G → ℂ), Continuous f → (∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) → IntegrableOn f 𝓕 μ := by
  intro G _ _ _ _ _ Γ _ K hK hcov μ hμ 𝓕 h𝓕 f hf hinv
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hbound : ∀ g, ‖f g‖ ≤ C := by
    intro g
    obtain ⟨γ, hγ, hγg⟩ := hcov g
    rw [← hinv γ hγ g]
    exact hC _ hγg
  have hcover : 𝓕 ⊆ ⋃ γ : Γ, (γ • K ∩ 𝓕) := by
    intro x hx
    obtain ⟨γ, hγ, hγx⟩ := hcov x
    refine Set.mem_iUnion.mpr ⟨(⟨γ, hγ⟩ : Γ)⁻¹, ?_, hx⟩
    rw [Set.mem_inv_smul_set_iff]
    exact hγx
  have hle : μ 𝓕 ≤ μ K :=
    calc μ 𝓕 ≤ μ (⋃ γ : Γ, (γ • K ∩ 𝓕)) := measure_mono hcover
      _ ≤ ∑' γ : Γ, μ (γ • K ∩ 𝓕) := measure_iUnion_le _
      _ = μ K := (h𝓕.measure_eq_tsum K).symm
  exact Measure.integrableOn_of_bounded (hle.trans_lt hK.measure_lt_top).ne
    hf.aestronglyMeasurable (M := C) (ae_of_all _ hbound)
end GlobalTheory
