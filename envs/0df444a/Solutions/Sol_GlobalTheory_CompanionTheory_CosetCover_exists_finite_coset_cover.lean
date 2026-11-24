-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:24:38.290967+00:00
-- url     : https://prove2.me/submissions/318e0882-e522-4bd5-a90c-a93bd2f07f0c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactSubgroupFiniteOpenCosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetCover
namespace GlobalTheory.CompanionTheory.CosetCover
theorem _root_.solution :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G),
      IsCompact (K₀ : Set G) → IsOpen (K : Set G) →
        ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  intro G _ _ _ K₀ K hK₀ hK
  classical
  obtain ⟨t, ht⟩ := hK₀.elim_finite_subcover
    (fun g : K₀ => (fun x => x * (g : G)⁻¹) ⁻¹' (K : Set G))
    (fun g => hK.preimage (continuous_mul_const _))
    (fun g hg => Set.mem_iUnion.2 ⟨⟨g, hg⟩, by simp⟩)
  refine ⟨t.card, fun i => ((t.equivFin.symm i : K₀) : G), fun i => (t.equivFin.symm i : K₀).2,
    fun g hg => ?_⟩
  obtain ⟨a, ha, hga⟩ := Set.mem_iUnion₂.1 (ht hg)
  refine ⟨t.equivFin ⟨a, ha⟩, g * (a : G)⁻¹, hga, ?_⟩
  simp
end GlobalTheory.CompanionTheory.CosetCover
