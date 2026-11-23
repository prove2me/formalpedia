-- Prove2me | solution 1 for GroundTheory.Automorphic.altSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:39:02.240716+00:00
-- url     : https://prove2.me/submissions/a0131e03-bd62-422e-b81a-80216fb61010

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
theorem _root_.solution (k : ℕ) (h : V → W) (y : Fin (k + 1) → V) (s : V) :
    altSum (k + 1) h y s = altSum k (fun t => h (t + y 0) - h t) (Fin.tail y) s := rfl
end GroundTheory.Automorphic
