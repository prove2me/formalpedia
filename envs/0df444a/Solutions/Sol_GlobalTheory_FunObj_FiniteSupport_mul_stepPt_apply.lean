-- Prove2me | solution 1 for GlobalTheory.FunObj.FiniteSupport.mul_stepPt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:47:14.002546+00:00
-- url     : https://prove2.me/submissions/2bd7a757-82b5-4571-8f07-9981d854029d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteUnfSupportOfNeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.FiniteSupport
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.RootEx.Supp GlobalTheory.RootEx.FJUnipotent
variable {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
omit [Fintype n'] [DecidableEq n']
namespace GlobalTheory.FunObj.FiniteSupport
theorem _root_.solution {b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (hb : b.BlockTriangular (midLev (c / 2)))
    (x₀ : Matrix n n' k) (e : StepVar n c n' → k) (r : n ⊕ Fin c) (j : Fin c)
    (h : symLev c r = symLev c (Sum.inr j : n ⊕ Fin c)) :
    (b * stepPt x₀ e) r (Sum.inr j.castSucc) = b r (Sum.inr j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr j)]
  · simp [stepPt, basePt, Free, Kept]
  · intro s _ hs
    by_cases hl : midLev (c / 2) s < midLev (c / 2) r
    · rw [hb hl, zero_mul]
    · unfold symLev at h
      rcases s with s | l
      · have : ¬ (c / 2 + 1 < j.val + 1 ∨ (Even c ∧ j.val = c / 2)) := by
          split_ifs at h with he <;> rcases r with r | r <;> simp [lev, midLev, he] at h hl ⊢ <;> omega
        have h0 : stepPt x₀ e (Sum.inl s) (Sum.inr j.castSucc) = 0 := by
          rw [stepPt, Matrix.add_apply, of_apply, dif_neg (by exact this)]; simp [basePt]
        rw [h0, mul_zero]
      · have h1 : ¬ l.val < j.val := by
          split_ifs at h with he <;> rcases r with r | r <;> simp [lev, midLev] at h hl ⊢ <;> omega
        have h2 : l.val ≠ j.val := fun e => hs (by rw [Fin.ext e])
        simp [stepPt, basePt, Free, Kept, h1, h2]
  · simp
end GlobalTheory.FunObj.FiniteSupport
