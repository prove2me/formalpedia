-- Prove2me | solution 1 for GlobalTheory.LocFlat.ColTranslate.affPt_add_colAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:35.586079+00:00
-- url     : https://prove2.me/submissions/1ddcca63-4f8f-41a0-a606-77500f4f8147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ContinuousWittExtendByZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatColumnMapEqRootExchangeOperatorTranslate
import Theorems.Thm_GlobalTheory_RootEx_Exchange_affPt_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.ColTranslate
open GlobalTheory.RootEx.Exchange GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat.ColTranslate
theorem _root_.solution {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    {c : ℕ} (q : Fin c) (y : n → k) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (q.val + 1) rs} → k) :
    affPt (q.val + 1) x₀ e + colAt n' c (q.val + 1) y = mat x₀ (ext0 (Free (q.val + 1)) e + gCol q y) := by
  classical
  ext r s
  rcases r with r | r <;> rcases s with s | s
  · simp [affPt_eq, mat, ext0, colAt, gCol, Free]
  · by_cases h : s = q.castSucc
    · subst h; simp [affPt_eq, mat, ext0, colAt, gCol, Free]
    · have h' : ¬ s.val = q.val := fun hh => h (Fin.ext (by simpa using hh))
      simp [affPt_eq, mat, ext0, colAt, gCol, h, h']
  · simp [affPt_eq, mat, ext0, colAt, gCol]
  · simp [affPt_eq, mat, ext0, colAt, gCol]
end GlobalTheory.LocFlat.ColTranslate
