-- Prove2me | solution 1 for GlobalTheory.RootEx.Model.free_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:08:03.323388+00:00
-- url     : https://prove2.me/submissions/a7406841-ac4f-4584-a3fe-d3248a0a8ced

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
theorem _root_.solution {n' : Type*} (p : ℕ) (hp : p ≤ c) (r : n ⊕ Fin c) :
    Free (n := n) (n' := n') p (r, Sum.inr (Fin.last c)) := by
  rcases r with r | r <;> simp [Free]
  omega
end GlobalTheory.RootEx.Model
