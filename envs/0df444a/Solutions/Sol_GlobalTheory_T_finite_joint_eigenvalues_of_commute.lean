-- Prove2me | solution 1 for GlobalTheory.T.finite_joint_eigenvalues_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:33:34.960919+00:00
-- url     : https://prove2.me/submissions/e54d8410-986a-47df-a7bd-ca5f96de5159

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystems
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteJointEigensystemsStatement
import Theorems.Thm_GlobalTheory_finite_joint_eigensystems


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K), (∀ i j, Commute (A i) (A j)) → Set.Finite {χ : ι → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, A i *ᵥ c = χ i • c} := by
  first | exact @GlobalTheory.finite_joint_eigensystems | exact GlobalTheory.finite_joint_eigensystems | (intros; apply GlobalTheory.finite_joint_eigensystems <;> assumption)
end _root_.GlobalTheory.T
