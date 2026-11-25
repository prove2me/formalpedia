-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZ.addCharEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:53.278446+00:00
-- url     : https://prove2.me/submissions/bac2e0de-1978-43fe-9b46-62a3b7174e17

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_TorsionDualFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Function
open GroundTheory.ProfCoh.QZ
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]
namespace GroundTheory.ProfCoh.QZ
theorem _root_.solution [Finite G] (f : G →+ QZ) (a : G) :
    addCharEquiv G f a = toComplex (f a) :=
  rfl
end GroundTheory.ProfCoh.QZ
