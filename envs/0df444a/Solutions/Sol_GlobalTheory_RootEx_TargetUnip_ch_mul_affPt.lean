-- Prove2me | solution 1 for GlobalTheory.RootEx.TargetUnip.ch_mul_affPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:19.099806+00:00
-- url     : https://prove2.me/submissions/37b4b92f-f61b-4e7b-a922-0f2d1a5dfa47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_mul_apply_of_inN
import Theorems.Thm_GlobalTheory_RootEx_TargetUnip_affPt_of_not_free

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
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.TargetUnip
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
omit [Fintype n'] [DecidableEq n']
namespace GlobalTheory.RootEx.TargetUnip
theorem _root_.solution {p : ℕ} {h : GL (n ⊕ Fin c) k} (hh : InN p h) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (h.val * affPt p x₀ e) = ch (affPt p x₀ e) + simpleSum h := by
  rw [ch, ch, simpleSum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_apply_of_inN hh, Fintype.sum_sum_type, Finset.sum_eq_zero, zero_add]
  · congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hl : lev (n := n) p (Sum.inr i) < lev (n := n) p (Sum.inr j)
    · rw [if_pos hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rw [if_neg hl]
      simp only [lev, Sum.elim_inr] at hl
      rw [if_neg (by omega)]
  · intro r _
    split_ifs with hl
    · simp only [lev, Sum.elim_inr, Sum.elim_inl] at hl
      rw [affPt_of_not_free _ _ _ (by simp only [Free, Fin.val_succ]; omega)]
      simp [basePt]
    · rfl
end GlobalTheory.RootEx.TargetUnip
