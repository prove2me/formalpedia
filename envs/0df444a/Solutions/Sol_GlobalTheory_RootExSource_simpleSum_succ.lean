-- Prove2me | solution 1 for GlobalTheory.RootExSource.simpleSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:05:00.826642+00:00
-- url     : https://prove2.me/submissions/33f122c3-d3ac-4df2-bb80-a17e26dde537

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
theorem _root_.solution (g : GL (n' ⊕ Fin (c + 1)) k) :
    simpleSum g = ∑ l : Fin c, g.val (Sum.inr l.castSucc) (Sum.inr l.succ) := by
  unfold simpleSum
  rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (s := Finset.univ) (f := fun j : Fin (c + 1) =>
    if j.val = (Fin.last c).val + 1 then g.val (Sum.inr (Fin.last c)) (Sum.inr j) else 0), add_zero]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_eq_single l.succ]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro h
      exact hj (Fin.ext (by simpa using h))
    · simp
  · intro j _
    rw [if_neg]
    have := j.2
    simp only [Fin.val_last]
    omega
end GlobalTheory.RootExSource
