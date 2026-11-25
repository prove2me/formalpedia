-- Prove2me | solution 1 for GroundTheory.Brauer.nonempty_algEquiv_matrix_of_algHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:22:33.34716+00:00
-- url     : https://prove2.me/submissions/cf94dd6b-b917-49db-8780-111c2428cfff

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {L : Type*} [Field L]
  [Algebra K L]
open RightMul
namespace GroundTheory.Brauer
theorem _root_.solution [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] (ι : L →ₐ[K] A) (h : finrank K L ^ 2 = finrank K A) :
    Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (finrank K L)) (Fin (finrank K L)) L) := by
  have hA : 0 < finrank K A := Module.finrank_pos
  have hL : 0 < finrank K L := by
    rcases Nat.eq_zero_or_pos (finrank K L) with h0 | h0
    · rw [h0] at h; omega
    · exact h0
  have : FiniteDimensional K L := Module.finite_of_finrank_pos hL
  have : Module.Finite L (RightMul ι) := Module.Finite.of_restrictScalars_finite K L _
  have hM : finrank L (RightMul ι) = finrank K L := by
    have h2 := Module.finrank_mul_finrank K L (RightMul ι)
    change finrank K L * finrank L (RightMul ι) = finrank K A at h2
    rw [← h, sq] at h2
    exact Nat.eq_of_mul_eq_mul_left hL h2
  have hinj : Function.Injective (actionHom ι) := RingHom.injective (actionHom ι).toRingHom
  have hdim : finrank L (L ⊗[K] A) = finrank L (Module.End L (RightMul ι)) := by
    rw [Module.finrank_baseChange, Module.finrank_linearMap, hM, ← h, sq]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (actionHom ι).toLinearMap) hdim).mp hinj
  exact ⟨(AlgEquiv.ofBijective (actionHom ι) ⟨hinj, hsurj⟩).trans
    (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq L (RightMul ι) hM))⟩
end GroundTheory.Brauer
