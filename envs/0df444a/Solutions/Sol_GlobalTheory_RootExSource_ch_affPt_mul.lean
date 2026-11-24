-- Prove2me | solution 1 for GlobalTheory.RootExSource.ch_affPt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:20:41.465955+00:00
-- url     : https://prove2.me/submissions/001c9a06-b0dd-4629-bb27-c54f9d6d9083

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Theorems.Thm_GlobalTheory_RootExSource_mul_apply_of_inN
import Theorems.Thm_GlobalTheory_RootExSource_affPt_nonfree
import Theorems.Thm_GlobalTheory_RootExSource_simpleSum_succ

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
theorem _root_.solution {g : GL (n' ⊕ Fin (c + 1)) k} (hg : InN p g) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    ch (affPt p x₀ e * g.val) = ch (affPt p x₀ e) + simpleSum g := by
  rw [simpleSum_succ, ch, ch, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_apply_of_inN hg, Finset.sum_eq_single (Sum.inr l.castSucc)]
  · rw [if_pos (by simp [lev]), affPt_nonfree _ _ _ (Sum.inr l.castSucc) (by simp [Free])]
    simp [basePt]
  · intro s' _ hs
    split_ifs with h'
    · have : ¬ Free p ((Sum.inr l : n ⊕ Fin c), s') ∧ basePt c x₀ (Sum.inr l) s' = 0 := by
        rcases s' with s' | s' <;> simp [Free, lev, basePt, Fin.ext_iff] at hs h' ⊢ <;> omega
      rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
    · rfl
  · simp
end GlobalTheory.RootExSource
