-- Prove2me | solution 1 for GroundTheory.GroupCoh.tateCup_of_pos_of_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:56:20.673656+00:00
-- url     : https://prove2.me/submissions/d1d6aa2a-847c-432b-befc-7fb3084b0905

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
theorem _root_.solution {p q : ℤ} (hp : 0 < p) (hq : q ≤ 0) :
    tateCup (k := k) (G := G) p q = tateCupR (tateCup p (q + 1)) := by
  rw [tateCup, dif_neg (by omega), dif_pos hq]
end GroundTheory.GroupCoh
