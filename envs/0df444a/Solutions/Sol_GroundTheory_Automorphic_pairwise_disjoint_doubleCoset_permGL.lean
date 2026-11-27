-- Prove2me | solution 1 for GroundTheory.Automorphic.pairwise_disjoint_doubleCoset_permGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:40.61384+00:00
-- url     : https://prove2.me/submissions/5a1f78a0-e6ce-49a5-9926-b8a36c696bff

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_doubleCoset_permGL_injective

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
    Pairwise (Function.onFun Disjoint fun σ : Equiv.Perm (Fin n) =>
      doubleCoset (permGL k σ) (borel n k) (borel n k)) := by
  intro σ τ hστ
  rw [Function.onFun, Set.disjoint_left]
  intro g hσ hτ
  exact hστ (doubleCoset_permGL_injective hσ hτ)
end GroundTheory.Automorphic
