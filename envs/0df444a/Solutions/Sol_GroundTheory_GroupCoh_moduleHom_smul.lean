-- Prove2me | solution 1 for GroundTheory.GroupCoh.moduleHom_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:08:23.963477+00:00
-- url     : https://prove2.me/submissions/a810f0a3-71a3-4b6e-be54-c409d1ae5cfe

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {M N : ModuleCat.{u} k} (f : M ⟶ N) (c : k) (y : M) :
    f.hom (c • y) = c • f.hom y :=
  map_smul _ _ _
end GroundTheory.GroupCoh
