-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.tateNorm_grMk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:55.163578+00:00
-- url     : https://prove2.me/submissions/68e59fc1-a399-4f28-9022-b073772668cc

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
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
variable [Fintype G]
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution {n : ℕ} (x : S.F n) :
    tateNorm G (S.gr n) (S.grMk n x) = S.grMk n (tateNorm G (S.F n) x) := by
  rw [tateNorm_apply, tateNorm_apply, map_prod]
  rfl
end GroundTheory.LocalField.StableFiltration
