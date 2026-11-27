-- Prove2me | solution 1 for GroundTheory.Automorphic.bijective_mk_permGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:44:38.538718+00:00
-- url     : https://prove2.me/submissions/7aed99c5-2618-4b9c-a7fa-6c702eaa18e3

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_exists_mem_doubleCoset_permGL
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
theorem _root_.solution :
    Function.Bijective fun σ : Equiv.Perm (Fin n) =>
      DoubleCoset.mk (borel n k) (borel n k) (permGL k σ) := by
  constructor
  · intro σ τ hστ
    obtain ⟨x, hx, y, hy, hxy⟩ := (DoubleCoset.eq _ _ _ _).mp hστ
    exact eq_of_permGL_mem_doubleCoset (mem_doubleCoset.mpr ⟨x, hx, y, hy, hxy⟩)
  · intro q
    obtain ⟨σ, hσ⟩ := exists_mem_doubleCoset_permGL (k := k) q.out
    refine ⟨σ, ?_⟩
    simp only
    rw [← mk_eq_of_doubleCoset_eq (doubleCoset_eq_of_mem hσ), out_eq']
end GroundTheory.Automorphic
