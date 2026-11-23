-- Prove2me | solution 1 for GroundTheory.Automorphic.conj_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:16:55.083797+00:00
-- url     : https://prove2.me/submissions/bd453d9d-03f7-4870-8823-9493b77ccd8f

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
theorem _root_.solution (c : F) : conj F E (algebraMap F E c) = algebraMap F E c :=
  conjLinear_algebraMap c
end GroundTheory.Automorphic
