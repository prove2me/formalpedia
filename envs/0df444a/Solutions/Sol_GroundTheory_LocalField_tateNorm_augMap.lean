-- Prove2me | solution 1 for GroundTheory.LocalField.tateNorm_augMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:28:31.13228+00:00
-- url     : https://prove2.me/submissions/a3687d79-f97a-4ac1-8b69-9ab4349b67c0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_augMap_apply
import Theorems.Thm_GroundTheory_LocalField_tateNorm_smul

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
variable {G M}
namespace GroundTheory.LocalField
theorem _root_.solution (m : G → M) : tateNorm G M (augMap G M m) = 1 := by
  rw [augMap_apply, map_prod]
  refine prod_eq_one fun g _ => ?_
  rw [map_div, tateNorm_smul, div_self']
end GroundTheory.LocalField
