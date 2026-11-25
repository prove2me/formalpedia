-- Prove2me | solution 1 for GroundTheory.LocalField.filtrationSeparated_of_hasBasis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:13:28.454805+00:00
-- url     : https://prove2.me/submissions/19dcb158-dcaf-4c63-8cfd-6eb9e20fe888

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Filter Topology Uniformity
namespace GroundTheory.LocalField
theorem _root_.solution {H : Type*} [Group H] [TopologicalSpace H] [T1Space H]
    {E : ℕ → Subgroup H}
    (hb : (𝓝 (1 : H)).HasBasis (fun _ => True) (fun n => (E n : Set H))) :
    FiltrationSeparated E := by
  intro g hg
  by_contra hne
  obtain ⟨i, -, hi⟩ := hb.mem_iff.mp
    (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr (Ne.symm hne)))
  exact hi (hg i) rfl
end GroundTheory.LocalField
