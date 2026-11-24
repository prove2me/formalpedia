-- Prove2me | solution 1 for GlobalTheory.FunObj.UnfModel.elt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:51:08.880533+00:00
-- url     : https://prove2.me/submissions/8d1b708d-a949-4cd2-af5e-f87f7c8079e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
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
open GlobalTheory GlobalTheory.FunObj GlobalTheory.FunObj.UnfModel
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.FunObj
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {G : Grid k} (hs : 1 ≤ G.s) [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k)
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FunObj.UnfModel
theorem _root_.solution (J : G.Level) :
    (Reps.through hs J fun _ => 1).elt (fun _ => DoubleCoset.mk _ _ 1) = 1 := by
  funext X
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    rw [Reps.elt, onColumn_apply]
    cases j with
    | zero => rfl
    | succ j => simp [Reps.through]
  · simp [Reps.elt, onColumn, hi]
end GlobalTheory.FunObj.UnfModel
