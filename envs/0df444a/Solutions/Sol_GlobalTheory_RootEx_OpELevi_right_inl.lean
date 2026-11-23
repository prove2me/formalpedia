-- Prove2me | solution 1 for GlobalTheory.RootEx.OpELevi.right_inl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:00:25.964231+00:00
-- url     : https://prove2.me/submissions/1cf890e9-1844-4ec6-8eb8-89e07e18deee

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
    (x * (fromBlocks A 0 0 1 : Matrix (n' ⊕ Fin (c + 1)) (n' ⊕ Fin (c + 1)) k)) r (Sum.inl s)
      = ∑ t, Aᵀ s t * x r (Sum.inl t) := by
  simp [Matrix.mul_apply, Fintype.sum_sum_type, mul_comm]
end GlobalTheory.RootEx.OpELevi
