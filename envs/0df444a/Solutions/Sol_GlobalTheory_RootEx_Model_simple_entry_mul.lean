-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.simple_entry_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:03:09.78891+00:00
-- url     : https://prove2.me/submissions/77ae6d3b-97ba-48c4-90c1-038e35326a5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Model
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.Model
theorem _root_.solution {p : ℕ} {g h : GL (n ⊕ Fin c) k} (hg : InN p g) (hh : InN p h) (i j : Fin c)
    (hij : j.val = i.val + 1) : (g * h).val (Sum.inr i) (Sum.inr j) =
      g.val (Sum.inr i) (Sum.inr j) + h.val (Sum.inr i) (Sum.inr j) := by
  have hne : (Sum.inr i : n ⊕ Fin c) ≠ Sum.inr j := by
    intro e; have := Sum.inr.inj e; subst this; omega
  rw [Units.val_mul, Matrix.mul_apply]
  have key : ∀ t : n ⊕ Fin c, g.val (Sum.inr i) t * h.val t (Sum.inr j) =
      (if t = Sum.inr j then g.val (Sum.inr i) (Sum.inr j) else 0) +
      (if t = Sum.inr i then h.val (Sum.inr i) (Sum.inr j) else 0) := by
    intro t
    have li : lev p (Sum.inr i : n ⊕ Fin c) = i.val + 1 := rfl
    have lj : lev p (Sum.inr j : n ⊕ Fin c) = j.val + 1 := rfl
    by_cases ht : lev p t ≤ i.val + 1
    · have htj : t ≠ Sum.inr j := by rintro rfl; omega
      rw [hg _ t (by omega)]
      by_cases hti : t = Sum.inr i
      · subst hti; simp [htj]
      · simp [htj, hti, Matrix.one_apply, Ne.symm hti]
    · have hti : t ≠ Sum.inr i := by rintro rfl; omega
      rw [hh t _ (by omega)]
      by_cases htj : t = Sum.inr j
      · subst htj; simp [hti]
      · simp [htj, hti, Matrix.one_apply]
  simp [key, Finset.sum_add_distrib]
end GlobalTheory.RootEx.Model
