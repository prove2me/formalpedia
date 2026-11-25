-- Prove2me | solution 1 for GroundTheory.Automorphic.coe_list_prod_transvectionGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:02:18.859455+00:00
-- url     : https://prove2.me/submissions/9175da04-4b48-46b3-a310-fe291ce8bce0

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
theorem _root_.solution (L : List (TransvectionStruct n R)) :
    (((L.map (transvectionGL n R)).prod : GL n R) : Matrix n n R) =
      (L.map TransvectionStruct.toMatrix).prod := by
  induction L with
  | nil => simp
  | cons t L ih => simp [ih]
end GroundTheory.Automorphic
