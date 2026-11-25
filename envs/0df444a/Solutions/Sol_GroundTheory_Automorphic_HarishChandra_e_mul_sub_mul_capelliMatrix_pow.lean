-- Prove2me | solution 1 for GroundTheory.Automorphic.HarishChandra.e_mul_sub_mul_capelliMatrix_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:49.989909+00:00
-- url     : https://prove2.me/submissions/c88b3e1a-1388-48d1-b8fd-aa55d518848c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_MemCenterOfCommuteE
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EMulSubMulCapelliMatrixPow
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Capelli
import Theorems.Thm_UpperTheory_Reformulated_B_Qk36_e_mul_sub_mul_capelliMatrix_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
variable {n : ℕ}
namespace GroundTheory.Automorphic.HarishChandra
theorem _root_.solution (a b : Fin n) (k : ℕ) (c d : Fin n) :
    e (a, b) * (capelliMatrix ^ k) c d - (capelliMatrix ^ k) c d * e (a, b) =
      (if b = c then (capelliMatrix ^ k) a d else 0) -
        (if d = a then (capelliMatrix ^ k) c b else 0) :=
  _root_.UpperTheory.Reformulated.B.Qk36.e_mul_sub_mul_capelliMatrix_pow a b k c d
end GroundTheory.Automorphic.HarishChandra
