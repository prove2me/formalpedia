-- Prove2me | solution 1 for GlobalTheory.RootExSource.mul_apply_of_inN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:08:38.627665+00:00
-- url     : https://prove2.me/submissions/506aa878-0283-4152-9320-05b97239d949

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal

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
open GlobalTheory GlobalTheory.RootExSource
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
  {c p : ℕ}
namespace GlobalTheory.RootExSource
theorem _root_.solution {m : Type} {g : GL (n' ⊕ Fin c) k} (hg : InN p g)
    (x : Matrix m (n' ⊕ Fin c) k) (r : m) (s : n' ⊕ Fin c) :
    (x * g.val) r s = x r s + ∑ s', if lev p s' < lev p s then x r s' * g.val s' s else 0 := by
  have : x r s = (x * (1 : Matrix (n' ⊕ Fin c) (n' ⊕ Fin c) k)) r s := by rw [Matrix.mul_one]
  rw [this, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s' _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne, mul_zero, zero_add]
    rintro rfl
    exact lt_irrefl _ h
  · rw [hg s' s (not_lt.1 h), add_zero]
end GlobalTheory.RootExSource
