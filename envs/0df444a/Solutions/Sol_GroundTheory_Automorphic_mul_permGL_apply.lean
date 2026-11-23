-- Prove2me | solution 1 for GroundTheory.Automorphic.mul_permGL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:29.243643+00:00
-- url     : https://prove2.me/submissions/85d064b5-f4ac-45dd-9070-95da01db8679

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_permGL_apply

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
theorem _root_.solution (M : Matrix (Fin n) (Fin n) k) (σ : Equiv.Perm (Fin n)) (r c : Fin n) :
    (M * (permGL k σ : Matrix (Fin n) (Fin n) k)) r c = M r (σ c) := by
  simp [mul_apply, permGL_apply]
end GroundTheory.Automorphic
