-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.smul_grMk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:54.870842+00:00
-- url     : https://prove2.me/submissions/a12f7458-78bd-4ae7-bae2-28d761593853

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
open GroundTheory.LocalField.StableFiltration
variable {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
  (S : StableFiltration G V)
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution {n : ℕ} (g : G) (x : S.F n) : g • S.grMk n x = S.grMk n (g • x) := rfl
end GroundTheory.LocalField.StableFiltration
