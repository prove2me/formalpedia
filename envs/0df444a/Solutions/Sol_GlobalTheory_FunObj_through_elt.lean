-- Prove2me | solution 1 for GlobalTheory.FunObj.through_elt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:44:40.755334+00:00
-- url     : https://prove2.me/submissions/163f99d3-c3c1-4fb1-93bf-576c9b5ab9bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Theorems.Thm_GlobalTheory_FunObj_onColumn_apply

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
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
variable {hs}
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
variable {J : G.Level} (keep : Bool) (ρ : Reps hs J) (T : G.Args → ℂ)
namespace GlobalTheory.FunObj
theorem _root_.solution (h : ∀ j : ℕ, GL (Fin (G.rank (G.m, j))) k) {j : ℕ} (hj : j + 2 ≤ G.m) :
    (Reps.through hs J h).elt (fun i => DoubleCoset.mk _ _ (h (i + 1))) (G.m, j) = h j := by
  rw [Reps.elt, onColumn_apply]
  cases j with
  | zero => rfl
  | succ i => simp [Reps.through, show i < G.m - 2 by omega]
end GlobalTheory.FunObj
