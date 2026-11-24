-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.inv_mul_affPt_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:03:17.233938+00:00
-- url     : https://prove2.me/submissions/474fabc1-bbb4-4557-bebb-641ee4981db7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
namespace GlobalTheory.RootEx.Supp
theorem _root_.solution {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n]
    [Fintype n'] [DecidableEq n'] {c p : ℕ} {b : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k}
    (hb : b.BlockTriangular (lev p)) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) (r : n ⊕ Fin c) (j : Fin c)
    (h : lev p r = lev p (Sum.inr j : n ⊕ Fin c)) :
    (b * affPt p x₀ e) r (Sum.inr j.castSucc) = b r (Sum.inr j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr j)]
  · simp [affPt, basePt, Free]
  · intro s _ hs
    by_cases hl : lev p s < lev p r
    · rw [hb hl, zero_mul]
    · rw [h] at hl
      rcases s with s | l
      · have : ¬ p < j.val + 1 := by simpa [lev] using hl
        simp [affPt, basePt, Free, this]
      · have h1 : ¬ l.val < j.val := by simpa [lev] using hl
        have h2 : l.val ≠ j.val := fun e => hs (by rw [Fin.ext e])
        simp [affPt, basePt, Free, h1, h2]
  · simp
end GlobalTheory.RootEx.Supp
