-- Prove2me | solution 1 for GroundTheory.Automorphic.coe_diagonalGL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:04.661858+00:00
-- url     : https://prove2.me/submissions/45856ea7-e1f1-43ad-9dd1-1185c62117cd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}
namespace GroundTheory.Automorphic
theorem _root_.solution (d : n → Rˣ) :
    (diagonalGL d : Matrix n n R) = diagonal fun k => (d k : R) := rfl
end GroundTheory.Automorphic
