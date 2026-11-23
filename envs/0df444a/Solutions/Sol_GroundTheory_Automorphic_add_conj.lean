-- Prove2me | solution 1 for GroundTheory.Automorphic.add_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:35.979843+00:00
-- url     : https://prove2.me/submissions/9decb2c4-2f2d-438b-824b-5e9bd3cd7759

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_QuadraticConj
import Theorems.Thm_GroundTheory_Automorphic_conj_apply

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
theorem _root_.solution (x : E) : x + conj F E x = algebraMap F E (Algebra.trace F E x) := by
  rw [conj_apply]; ring
end GroundTheory.Automorphic
