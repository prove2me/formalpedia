-- Prove2me | solution 1 for GlobalTheory.RootExSource.affPt_mul_nonfree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:04:59.119374+00:00
-- url     : https://prove2.me/submissions/e60cb07d-a4e7-492a-ae29-cadd836edd58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SecondCountableLocal
import Theorems.Thm_GlobalTheory_RootExSource_mul_apply_of_inN
import Theorems.Thm_GlobalTheory_RootExSource_affPt_nonfree

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
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k)
    (r s) (h : ¬ Free p (r, s)) : (affPt p x₀ e * g.val) r s = basePt c x₀ r s := by
  rw [mul_apply_of_inN hg, affPt_nonfree _ _ _ _ h, Finset.sum_eq_zero, add_zero]
  intro s' _
  split_ifs with h'
  · have : ¬ Free p (r, s') ∧ basePt c x₀ r s' = 0 := by
      rcases r with r | r <;> rcases s with s | s <;> rcases s' with s' | s' <;>
        simp [Free, lev, basePt] at h h' ⊢ <;> omega
    rw [affPt_nonfree _ _ _ _ this.1, this.2, zero_mul]
  · rfl
end GlobalTheory.RootExSource
