-- Prove2me | solution 1 for GroundTheory.LocalField.mem_invariants
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:22.458795+00:00
-- url     : https://prove2.me/submissions/e23732f5-2b05-47b6-899a-432c34aba70d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial

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
open Finset Filter
variable (G M : Type*) [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
omit [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution {x : M} : x ∈ invariants G M ↔ ∀ g : G, g • x = x := Iff.rfl
end GroundTheory.LocalField
