-- Prove2me | solution 1 for GroundTheory.ProfCoh.QZ.evalHom_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:51:56.548788+00:00
-- url     : https://prove2.me/submissions/acb5212d-1c1f-4b87-bdb9-6843ff4388f2

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
theorem _root_.solution (a : G) (f : G →+ QZ) : evalHom G a f = f a :=
  rfl
end GroundTheory.ProfCoh.QZ
