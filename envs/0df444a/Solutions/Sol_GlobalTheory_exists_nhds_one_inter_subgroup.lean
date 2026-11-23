-- Prove2me | solution 1 for GlobalTheory.exists_nhds_one_inter_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:25.277336+00:00
-- url     : https://prove2.me/submissions/a62fe55c-c94c-4fd7-8c33-0051a4ba6e96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsFundamentalDomainAndQuotMeasureEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal
open GlobalTheory
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] (Γ : Subgroup G) [DiscreteTopology Γ]
omit [IsTopologicalGroup G] [SecondCountableTopology G]
namespace GlobalTheory
theorem _root_.solution : ∃ V ∈ 𝓝 (1 : G), ∀ g ∈ Γ, g ∈ V → g = 1 := by
  have h : ({1} : Set Γ) ∈ 𝓝 (1 : Γ) := (isOpen_discrete _).mem_nhds rfl
  rw [nhds_induced, mem_comap] at h
  obtain ⟨V, hV, h⟩ := h
  exact ⟨V, hV, fun g hg hgV => congrArg Subtype.val (h (a := ⟨g, hg⟩) hgV)⟩
end GlobalTheory
