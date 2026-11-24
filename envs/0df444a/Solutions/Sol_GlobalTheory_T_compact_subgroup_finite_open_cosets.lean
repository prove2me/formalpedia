-- Prove2me | solution 1 for GlobalTheory.T.compact_subgroup_finite_open_cosets
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:05:03.472267+00:00
-- url     : https://prove2.me/submissions/67e23f64-4e64-4a5c-a242-febbed61b697

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactSubgroupFiniteOpenCosets
import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactSubgroupFiniteOpenCosetsStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CosetCover_exists_finite_coset_cover


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G), IsCompact (K₀ : Set G) → IsOpen (K : Set G) → ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by
  first | exact @GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | exact GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover | (intros; apply GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover <;> assumption)
end _root_.GlobalTheory.T
