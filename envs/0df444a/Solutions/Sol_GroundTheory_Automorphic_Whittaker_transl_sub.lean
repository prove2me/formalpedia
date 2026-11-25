-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.transl_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:10.33571+00:00
-- url     : https://prove2.me/submissions/3f8b19cf-6a3f-4120-bc4d-048a2c1fc5dd

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
theorem _root_.solution (h : H) (f g : X → ℂ) : transl h (f - g) = transl h f - transl h g := rfl
end GroundTheory.Automorphic.Whittaker
