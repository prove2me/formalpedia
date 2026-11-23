-- Prove2me | solution 1 for GroundTheory.Automorphic.one_add_vecMulVec_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:16.281675+00:00
-- url     : https://prove2.me/submissions/55c4f129-56cf-4903-b1da-84312e12383b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) k) (i : Fin n) (u : Fin n → k)
    (r c : Fin n) :
    ((1 + vecMulVec u (Pi.single i 1)) * M) r c = M r c + u r * M i c := by
  simp [Matrix.add_mul, vecMulVec_mul, vecMulVec_apply]
end GroundTheory.Automorphic
