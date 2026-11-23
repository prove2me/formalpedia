-- Prove2me | solution 1 for GroundTheory.Automorphic.doubleCoset_permGL_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:38.65644+00:00
-- url     : https://prove2.me/submissions/cff6b561-c13b-4ca6-a6af-6cb247c64c0e

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
theorem _root_.solution {σ τ : Equiv.Perm (Fin n)} {g : GL (Fin n) k}
    (hσ : g ∈ doubleCoset (permGL k σ) (borel n k) (borel n k))
    (hτ : g ∈ doubleCoset (permGL k τ) (borel n k) (borel n k)) : σ = τ := by
  have e : doubleCoset (permGL k σ) (borel n k) (borel n k) =
      doubleCoset (permGL k τ) (borel n k) (borel n k) :=
    (doubleCoset_eq_of_mem hσ).symm.trans (doubleCoset_eq_of_mem hτ)
  have hmem := mem_doubleCoset_self (borel n k) (borel n k) (permGL k τ)
  rw [← e] at hmem
  exact eq_of_permGL_mem_doubleCoset hmem
end GroundTheory.Automorphic
