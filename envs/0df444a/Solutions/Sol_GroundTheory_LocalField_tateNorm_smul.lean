-- Prove2me | solution 1 for GroundTheory.LocalField.tateNorm_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:15:31.374041+00:00
-- url     : https://prove2.me/submissions/15b417f0-00fe-4537-a2af-27a674ba05e7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Theorems.Thm_GroundTheory_LocalField_tateNorm_apply

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
theorem _root_.solution (g : G) (x : M) : tateNorm G M (g • x) = tateNorm G M x := by
  simp_rw [tateNorm_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)
end GroundTheory.LocalField
