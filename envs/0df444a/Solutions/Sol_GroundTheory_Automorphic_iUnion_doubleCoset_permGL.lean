-- Prove2me | solution 1 for GroundTheory.Automorphic.iUnion_doubleCoset_permGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:48:06.25821+00:00
-- url     : https://prove2.me/submissions/c0f9a1e3-def3-4e4d-8382-81c8c58003b1

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_doubleCoset_permGL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset
variable {n : ℕ} {k : Type*} [Field k]
namespace GroundTheory.Automorphic
theorem _root_.solution :
    ⋃ σ : Equiv.Perm (Fin n), doubleCoset (permGL k σ) (borel n k) (borel n k) = Set.univ :=
  Set.eq_univ_of_forall fun g => Set.mem_iUnion.mpr (exists_mem_doubleCoset_permGL g)
end GroundTheory.Automorphic
