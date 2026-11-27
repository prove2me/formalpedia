-- Prove2me | solution 2 for GroundTheory.Automorphic.permGL_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:43.664974+00:00
-- url     : https://prove2.me/submissions/8c3c5643-a5b5-4889-992f-1d810514f9fc

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_eq_of_permGL_mem_doubleCoset

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
theorem _root_.solution : Function.Injective (permGL k : Equiv.Perm (Fin n) → GL (Fin n) k) := by
  intro σ τ h
  apply eq_of_permGL_mem_doubleCoset (k := k)
  rw [← h]
  exact mem_doubleCoset_self _ _ _
end GroundTheory.Automorphic
