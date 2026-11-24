-- Prove2me | solution 1 for GroundTheory.Automorphic.Whittaker.transl_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:36.774146+00:00
-- url     : https://prove2.me/submissions/64c4f091-d0ac-4737-b752-d6f13ac6f0a2

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
theorem _root_.solution (h : H) (f g : X → ℂ) : transl h (f + g) = transl h f + transl h g := rfl
end GroundTheory.Automorphic.Whittaker
