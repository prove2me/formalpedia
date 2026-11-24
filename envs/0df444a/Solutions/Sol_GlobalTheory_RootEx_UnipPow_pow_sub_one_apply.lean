-- Prove2me | solution 1 for GlobalTheory.RootEx.UnipPow.pow_sub_one_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:11:19.113924+00:00
-- url     : https://prove2.me/submissions/cbe10de1-4af0-4a1b-a870-f3308e6b1e4e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentExistsResidueCardPowMemNhds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.UnipPow
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootEx.UnipPow
theorem _root_.solution {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
    {g : GL (n ⊕ Fin c) K} (hg : InN p g) (j : ℕ) :
    ∀ r s : n ⊕ Fin c, lev p s < lev p r + j →
      (((g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) K) - 1) ^ j) r s = 0 := by
  induction j with
  | zero =>
    intro r s h
    rw [pow_zero, Matrix.one_apply_ne (by rintro rfl; omega)]
  | succ j ih =>
    intro r s h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : lev p t < lev p r + j
    · rw [ih r t ht, zero_mul]
    · rw [Matrix.sub_apply, hg t s (by omega), sub_self, mul_zero]
end GlobalTheory.RootEx.UnipPow
