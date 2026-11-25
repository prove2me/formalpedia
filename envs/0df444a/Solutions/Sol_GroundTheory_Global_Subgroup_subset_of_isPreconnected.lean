-- Prove2me | solution 1 for GroundTheory.Global.Subgroup.subset_of_isPreconnected
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:36:22.569667+00:00
-- url     : https://prove2.me/submissions/f38705eb-aa86-4539-be23-b5d3171cf9f4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_OpenSubgroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
namespace GroundTheory.Global
namespace Subgroup
theorem _root_.solution {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G)) {s : Set G}
    (hs : IsPreconnected s) (h1 : (1 : G) ∈ s) : s ⊆ H :=
  hs.subset_isClopen ⟨H.isClosed_of_isOpen hH, hH⟩ ⟨1, h1, H.one_mem⟩
end Subgroup
end GroundTheory.Global
