-- Prove2me | solution 1 for GroundTheory.Automorphic.mul_transvection_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:04:19.708108+00:00
-- url     : https://prove2.me/submissions/b61bf8d9-1a38-475f-9060-afef2ad46ac0

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
theorem _root_.solution (i j : n) (c : R) (M : Matrix n n R) (a b : n) :
    (M * transvection i j c) a b = if b = j then M a j + c * M a i else M a b := by
  split_ifs with h
  · subst h
    exact mul_transvection_apply_same i b a c M
  · exact mul_transvection_apply_of_ne i j a b h c M
end GroundTheory.Automorphic
