-- Prove2me | solution 1 for GroundTheory.Automorphic.permGL_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:39:40.949803+00:00
-- url     : https://prove2.me/submissions/48efb842-13b8-412a-b3b4-7641551223a6

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
    ((permGL k σ : Matrix (Fin n) (Fin n) k) * M) r c = M (σ⁻¹ r) c := by
  rw [mul_apply, Fintype.sum_eq_single (σ⁻¹ r)]
  · simp [permGL_apply]
  · intro a ha
    rw [permGL_apply, if_neg, zero_mul]
    rintro rfl
    exact ha (by simp)
end GroundTheory.Automorphic
