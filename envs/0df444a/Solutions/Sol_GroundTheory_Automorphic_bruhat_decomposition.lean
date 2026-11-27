-- Prove2me | solution 1 for GroundTheory.Automorphic.bruhat_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:41.504663+00:00
-- url     : https://prove2.me/submissions/e295d8c8-6c2f-4a3c-89fa-a7f38a39e085

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_doubleCoset_permGL
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
theorem _root_.solution (g : GL (Fin n) k) :
    ∃! σ : Equiv.Perm (Fin n), g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k) := by
  obtain ⟨σ, hσ⟩ := exists_mem_doubleCoset_permGL g
  exact ⟨σ, hσ, fun τ hτ => (doubleCoset_permGL_injective hσ hτ).symm⟩
end GroundTheory.Automorphic
