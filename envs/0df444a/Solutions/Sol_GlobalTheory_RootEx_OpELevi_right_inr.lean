-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.right_inr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:32.0258+00:00
-- url     : https://prove2.me/submissions/46c7d29a-e770-4f44-80cf-d5bf2cb24c61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralCompBlocks

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.OpELevi
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n] [DecidableEq n] [DecidableEq n']
namespace GlobalTheory.RootEx.OpELevi
theorem _root_.solution (A : Matrix n' n' k) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (r s) :
    (x * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) r (Sum.inr s)
      = x r (Sum.inr s) := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp only [fromBlocks_apply₁₂, fromBlocks_apply₂₂, Matrix.zero_apply, mul_zero,
    Finset.sum_const_zero, zero_add, Matrix.one_apply, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
end GlobalTheory.RootEx.OpELevi
