-- Prove2me | solution 1 for GroundTheory.Brauer.exists_algEquiv_matrix_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:24:05.197547+00:00
-- url     : https://prove2.me/submissions/412e2d08-9f42-4e55-930e-1497dfd9fa14

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_Degree
import Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
import Theorems.Thm_GroundTheory_Brauer_finrank_baseChange_eq
import Theorems.Thm_GroundTheory_Brauer_tensorCSA_carrier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Brauer.baseChangeTensor_tmul
attribute [local simp] GroundTheory.Brauer.tensorCSA_carrier



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open Module TensorProduct
universe u v w
variable (K : Type u) [Field K] (A : Type v) [Ring A] [Algebra K A]
namespace GroundTheory.Brauer
theorem _root_.solution [Algebra.IsCentral K A] [IsSimpleRing A]
    [FiniteDimensional K A] :
    ∃ n : ℕ, NeZero n ∧ finrank K A = n ^ 2 ∧
      Nonempty (AlgebraicClosure K ⊗[K] A ≃ₐ[AlgebraicClosure K]
        Matrix (Fin n) (Fin n) (AlgebraicClosure K)) := by
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed
    (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] A)
  refine ⟨n, hn, ?_, ⟨e⟩⟩
  rw [← finrank_baseChange_eq K (AlgebraicClosure K) A, e.toLinearEquiv.finrank_eq,
    Module.finrank_matrix, Module.finrank_self]
  simp [sq]
end GroundTheory.Brauer
