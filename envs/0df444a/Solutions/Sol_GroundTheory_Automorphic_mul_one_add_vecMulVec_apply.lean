-- Prove2me | solution 1 for GroundTheory.Automorphic.mul_one_add_vecMulVec_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:15.988461+00:00
-- url     : https://prove2.me/submissions/dab2193f-22fb-4db7-ba7f-a286fa98881e

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) k) (j : Fin n) (v : Fin n → k)
    (r c : Fin n) :
    (M * (1 + vecMulVec (Pi.single j 1) v)) r c = M r c + M r j * v c := by
  simp [Matrix.mul_add, mul_vecMulVec, vecMulVec_apply]
end GroundTheory.Automorphic
