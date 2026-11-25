-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.tateNorm_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:13:20.992915+00:00
-- url     : https://prove2.me/submissions/442b0c70-f026-4d0c-addb-3d23cfceb36e

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
variable [Fintype G]
namespace GroundTheory.LocalField.StableFiltration
theorem _root_.solution {n : ℕ} {x : V} (hx : x ∈ S.F n) : tateNorm G V x ∈ S.F n :=
  Subgroup.prod_mem _ fun g _ => S.smul_mem n g hx
end GroundTheory.LocalField.StableFiltration
