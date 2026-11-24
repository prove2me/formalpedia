-- Prove2me | solution 1 for GlobalTheory.FunObj.UnfModel.moved_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:06.787352+00:00
-- url     : https://prove2.me/submissions/69f6e725-6bd5-4a9f-b56c-c91e955bea85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_MiddleNotMem
import Theorems.Thm_GlobalTheory_SplitFlip_Grid_pathAct_one


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
omit [MeasurableSpace k] [BorelSpace k]
namespace GlobalTheory.FunObj.UnfModel
theorem _root_.solution (keep : Bool) (T : G.Args → ℂ) : moved G keep 1 T = T := by
  funext z
  have : charFactor G 1 = 1 := by simp [charFactor]
  cases keep <;> simp [moved, Grid.pathAct_one, this]
end GlobalTheory.FunObj.UnfModel
