-- Prove2me | solution 1 for GlobalTheory.T.trace_lift_monomialMatrix_eq_sum_eigenvalues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:49:51.314993+00:00
-- url     : https://prove2.me/submissions/b9b64603-35d7-46bc-8184-475ae1bd5879

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_TraceLiftMonomialMatrixEqSumEigenvalues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_TraceLiftMonomialMatrixEqSumEigenvaluesStatement
import Theorems.Thm_GlobalTheory_MonoTrace_trace_lift_monomial


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] [IsAlgClosed k] (θ : k →* ℂ), (∀ x y : k, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) → ∀ (n N : ℕ) (σ : Equiv.Perm (Fin n)) (c : Fin n → k), (∀ j, c j ≠ 0) → (N : k) ≠ 0 → (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k) ^ N = 1 → (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) ^ N = 1 → Matrix.trace (Matrix.of fun i j => if i = σ j then θ (c j) else 0 : Matrix (Fin n) (Fin n) ℂ) = ((Matrix.charpoly (Matrix.of fun i j => if i = σ j then c j else 0 : Matrix (Fin n) (Fin n) k)).roots.map θ).sum := by
  first | exact @GlobalTheory.MonoTrace.trace_lift_monomial | exact GlobalTheory.MonoTrace.trace_lift_monomial | (intros; apply GlobalTheory.MonoTrace.trace_lift_monomial <;> assumption)
end _root_.GlobalTheory.T
