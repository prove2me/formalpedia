-- Prove2me | solution 1 for GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:23:52.741918+00:00
-- url     : https://prove2.me/submissions/1566b0fb-c07f-4843-b728-5e1896e8bfe2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_FrobeniusTorusMinpolyDegreeRootPowerSumStatement
import Theorems.Thm_GlobalTheory_CuspGL_torus_minpoly


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
theorem _root_.solution : ∀ (F : Type) [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (n : ℕ), 0 < n → ∀ α ∈ {α : AlgebraicClosure F | α ^ (Nat.card F ^ n - 1) = 1}, (minpoly F α).natDegree ∣ n ∧ (minpoly F α).coeff 0 ≠ 0 ∧ ∀ k : ℕ, rootSum θ k (minpoly F α ^ (n / (minpoly F α).natDegree)) = ∑ i ∈ Finset.range n, θ (α ^ Nat.card F ^ i) ^ k := by
  first | exact @GlobalTheory.CuspGL.torus_minpoly | exact GlobalTheory.CuspGL.torus_minpoly | (intros; apply GlobalTheory.CuspGL.torus_minpoly <;> assumption)
end _root_.GlobalTheory.T
