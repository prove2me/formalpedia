-- Prove2me | solution 1 for GlobalTheory.T.echelon_projector_kernel_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:15:24.598687+00:00
-- url     : https://prove2.me/submissions/0a1667c8-3c55-4e0e-a4cd-442e31e1ad48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EchelonProjectorKernelFrobenius
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EchelonProjectorKernelFrobeniusStatement
import Theorems.Thm_GlobalTheory_echelon_projector_frobenius


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped NNReal
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) [Fact l.Prime] (C : Type) [Field C] [CharP C l] (d : ℕ) (Y A : Matrix (Fin d) (Fin d) C), A.det ≠ 0 → Y.map (frobenius C l) = Y * A → ∃ (I : Finset (Fin d)) (Q Λ : Matrix (Fin d) (Fin d) C), Y * Q = 0 ∧ (∀ v, Y.mulVec v = 0 → Q.mulVec v = v) ∧ (∀ i ∈ I, ∀ j, Q i j = if i = j then 1 else 0) ∧ (∀ i, ∀ j ∉ I, Q i j = 0) ∧ Q = A * Q.map (frobenius C l) * Λ := by
  first | exact @GlobalTheory.echelon_projector_frobenius | exact GlobalTheory.echelon_projector_frobenius | (intros; apply GlobalTheory.echelon_projector_frobenius <;> assumption)
end _root_.GlobalTheory.T
