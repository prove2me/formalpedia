-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_eq_mul_permGL_of_rowsReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:03:04.786521+00:00
-- url     : https://prove2.me/submissions/1a2c28e9-020a-4f5f-8d60-96b24c1818f6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Theorems.Thm_GroundTheory_Automorphic_mul_permGL_apply
import Theorems.Thm_GroundTheory_Automorphic_exists_borel_of_isUpperTriangular

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
theorem _root_.solution (g : GL (Fin n) k)
    (hred : RowsReduced (g : Matrix (Fin n) (Fin n) k) 0) :
    ∃ σ : Equiv.Perm (Fin n), ∃ b ∈ borel n k, g = b * permGL k σ := by
  classical
  obtain ⟨p, hp⟩ := hred
  have hinj : Function.Injective p := by
    intro i i' e
    by_contra hii
    exact (hp i' (Nat.zero_le _)).1 (e ▸ (hp i (Nat.zero_le _)).2.2 i' (Ne.symm hii))
  set τ : Equiv.Perm (Fin n) := Equiv.ofBijective p (Finite.injective_iff_bijective.mp hinj)
  have hτ : ∀ i, τ i = p i := fun i => rfl
  set d : Fin n → k := fun i => (g : Matrix (Fin n) (Fin n) k) i (p i)
  obtain ⟨b, hb, hbD⟩ := exists_borel_of_isUpperTriangular (diagonal d)
    (blockTriangular_diagonal d) (fun i => by simpa [d] using (hp i (Nat.zero_le _)).1)
  refine ⟨τ⁻¹, b, hb, ?_⟩
  ext r c
  rw [Units.val_mul, mul_permGL_apply, hbD, diagonal_apply]
  by_cases hc : c = p r
  · subst hc
    rw [if_pos (by rw [← hτ]; simp)]
  · rw [(hp r (Nat.zero_le _)).2.1 c hc, if_neg]
    intro e
    apply hc
    rw [← hτ, e]
    simp
end GroundTheory.Automorphic
