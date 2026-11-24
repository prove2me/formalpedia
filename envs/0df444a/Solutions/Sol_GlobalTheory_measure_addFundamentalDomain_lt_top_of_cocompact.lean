-- Prove2me | solution 1 for GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:50:07.239235+00:00
-- url     : https://prove2.me/submissions/dacedf7a-cbb7-4e29-bf82-26b27bff5eae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MeanSquareAddFundamentalDomainOfCocompact

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
theorem _root_.solution {G : Type} [AddGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x : G, ∃ γ ∈ Γ, γ + x ∈ K) (μ : Measure G) [μ.IsAddHaarMeasure] {F : Set G}
    (hF : IsAddFundamentalDomain Γ F μ) : μ F < ⊤ := by
  have hsub : F ⊆ ⋃ γ : Γ, ((γ +ᵥ K) ∩ F) := by
    intro g hg
    obtain ⟨γ, hγ, hk⟩ := hcov g
    refine Set.mem_iUnion.2 ⟨-(⟨γ, hγ⟩ : Γ), ?_, hg⟩
    rw [Set.mem_neg_vadd_set_iff]
    exact hk
  calc μ F ≤ μ (⋃ γ : Γ, ((γ +ᵥ K) ∩ F)) := measure_mono hsub
    _ ≤ ∑' γ : Γ, μ ((γ +ᵥ K) ∩ F) := measure_iUnion_le _
    _ = μ K := (hF.measure_eq_tsum K).symm
    _ < ⊤ := hK.measure_lt_top
end GlobalTheory
