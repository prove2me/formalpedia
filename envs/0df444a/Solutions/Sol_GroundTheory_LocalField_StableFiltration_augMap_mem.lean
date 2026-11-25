-- Prove2me | solution 1 for GroundTheory.LocalField.StableFiltration.augMap_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:35.494665+00:00
-- url     : https://prove2.me/submissions/df1ddcdb-234d-415e-9a6b-4f1552945295

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
theorem _root_.solution {n : ℕ} {m : G → V} (hm : ∀ g, m g ∈ S.F n) : augMap G V m ∈ S.F n :=
  Subgroup.prod_mem _ fun g _ => Subgroup.div_mem _ (S.smul_mem n g (hm g)) (hm g)
end GroundTheory.LocalField.StableFiltration
