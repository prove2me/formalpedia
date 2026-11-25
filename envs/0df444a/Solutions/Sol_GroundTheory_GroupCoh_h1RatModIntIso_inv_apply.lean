-- Prove2me | solution 1 for GroundTheory.GroupCoh.h1RatModIntIso_inv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:49:23.752401+00:00
-- url     : https://prove2.me/submissions/114d2e64-e9f6-4be7-be31-9a24e3072805

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
import Definitions.Def_GroundTheory_TateCohomology_Characters

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep groupCohomology
variable (G : Type) [Group G] [Fintype G]
omit [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (χ : Additive G →+ AddCircle (1 : ℚ)) :
    (h1RatModIntIso G).inv χ =
      H1π _ ((cocycles₁IsoOfIsTrivial (Rep.trivial ℤ G (AddCircle (1 : ℚ)))).inv χ) :=
  rfl
end GroundTheory.GroupCoh
