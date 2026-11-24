-- Prove2me | solution 1 for GlobalTheory.FunObj.Kept.not_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:58.549978+00:00
-- url     : https://prove2.me/submissions/4effef4c-0235-48b4-a919-abdb9aaef0bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum

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
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)
variable {k n c}
variable {n' : Type*} [Fintype n'] [DecidableEq n']
omit [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.FunObj
namespace Kept
theorem _root_.solution {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1))} (h : Kept rs) : ¬ Free (c / 2 + 1) rs := by
  rcases rs with ⟨r | r, s | s⟩ <;> simp only [Kept, Free] at h ⊢ <;> omega
end Kept
end GlobalTheory.FunObj
