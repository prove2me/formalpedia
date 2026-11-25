-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.transl_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:01:58.695697+00:00
-- url     : https://prove2.me/submissions/6baf8f46-57e1-42de-be2f-4378733433bc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Set Topology MulAction
open scoped Pointwise
variable {X : Type*} {H : Type*} [Group H] [MulAction H X]
namespace GroundTheory.Automorphic.Whittaker
theorem _root_.solution (h : H) (c : ℂ) (f : X → ℂ) : transl h (c • f) = c • transl h f := rfl
end GroundTheory.Automorphic.Whittaker
