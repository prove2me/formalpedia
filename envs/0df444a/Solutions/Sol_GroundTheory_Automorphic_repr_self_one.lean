-- Prove2me | solution 1 for GroundTheory.Automorphic.repr_self_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:04:16.507184+00:00
-- url     : https://prove2.me/submissions/11a1c2d7-311b-4acf-8dbf-e28d9bd4fd02

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E]
variable {F E}
variable [Algebra.IsQuadraticExtension F E]
namespace GroundTheory.Automorphic
theorem _root_.solution {x : E} (hx : x ∉ Set.range (algebraMap F E)) :
    (basisOneOf hx).repr x 1 = 1 := by
  have h := (basisOneOf hx).repr_self 1
  rw [basisOneOf_one] at h
  rw [h]; simp
end GroundTheory.Automorphic
