-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.X_mem_laurentSubalgebra
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:28:11.695867+00:00
-- url     : https://prove2.me/submissions/e696e922-1136-45a2-96d0-0f90464f97f3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution : (RatFunc.X : RatFunc ℂ) ∈ laurentSubalgebra :=
  Algebra.subset_adjoin (Set.mem_insert _ _)
end GroundTheory.Automorphic.GodementJacquet
