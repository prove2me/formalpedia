-- Prove2me | solution 1 for GroundTheory.Automorphic.altSum_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:07:01.631811+00:00
-- url     : https://prove2.me/submissions/ac1e2071-091b-404a-a732-a0ceef801959

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalDiscreteness_AltSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GroundTheory GroundTheory.Automorphic
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]
namespace GroundTheory.Automorphic
theorem _root_.solution (h : V → W) (y : Fin 0 → V) (s : V) : altSum 0 h y s = h s := rfl
end GroundTheory.Automorphic
