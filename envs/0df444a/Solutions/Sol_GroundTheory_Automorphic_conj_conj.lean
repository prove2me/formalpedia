-- Prove2me | solution 1 for GroundTheory.Automorphic.conj_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:28.907806+00:00
-- url     : https://prove2.me/submissions/e17a0d15-781d-4dd2-92b2-8739d5712592

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
theorem _root_.solution (x : E) : conj F E (conj F E x) = x := conjLinear_conjLinear x
end GroundTheory.Automorphic
