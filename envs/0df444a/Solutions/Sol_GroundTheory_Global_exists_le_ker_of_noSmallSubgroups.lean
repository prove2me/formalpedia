-- Prove2me | solution 1 for GroundTheory.Global.exists_le_ker_of_noSmallSubgroups
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:04.38191+00:00
-- url     : https://prove2.me/submissions/97ff72e5-e978-4505-9d31-afdf07fcbb0b

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Topology Filter IsDedekindDomain WithZero
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution {G H : Type*} [Group G] [TopologicalSpace G] [Group H]
    [TopologicalSpace H] {P : Subgroup G → Prop}
    (hP : ∀ W ∈ 𝓝 (1 : G), ∃ L : Subgroup G, P L ∧ (L : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (χ : G →* H) (hχ : Continuous χ) : ∃ L : Subgroup G, P L ∧ L ≤ χ.ker := by
  obtain ⟨U, hU, hsmall⟩ := hH
  have hW : χ ⁻¹' U ∈ 𝓝 (1 : G) := hχ.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨L, hL, hLW⟩ := hP _ hW
  refine ⟨L, hL, ?_⟩
  rw [← Subgroup.map_eq_bot_iff]
  refine hsmall _ ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hLW hx
end GroundTheory.Global
