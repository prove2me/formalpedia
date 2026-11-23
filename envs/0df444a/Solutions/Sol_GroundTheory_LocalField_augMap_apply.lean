-- Prove2me | solution 1 for GroundTheory.LocalField.augMap_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:22.680187+00:00
-- url     : https://prove2.me/submissions/3f1ca96c-697a-4379-8470-f00dcf4ef1b6

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
namespace GroundTheory.LocalField
theorem _root_.solution (m : G → M) : augMap G M m = ∏ g : G, g • m g / m g := rfl
end GroundTheory.LocalField
