-- Prove2me | solution 1 for GroundTheory.Automorphic.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:01.808101+00:00
-- url     : https://prove2.me/submissions/c1fe143b-ddfe-4b2a-81be-fb8f4dc01293

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
theorem _root_.solution (x : E) : conj F E x = algebraMap F E (Algebra.trace F E x) - x := rfl
end GroundTheory.Automorphic
