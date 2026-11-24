-- Prove2me | solution 1 for GlobalTheory.TwistVertex.level_lam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:27:08.415806+00:00
-- url     : https://prove2.me/submissions/ba4c9ed7-e9cb-4851-b1a7-45a0c1a18d49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FirstVertexParahoricLevelChainTwist
import Theorems.Thm_GlobalTheory_StepData_Level_map_lam
import Theorems.Thm_GlobalTheory_StepData_parahoric_lam


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.TwistVertex
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r e n : Type*} [Fintype r] [DecidableEq r] [Fintype e] [DecidableEq e] [IsEmpty e]
  [Fintype n] [DecidableEq n] {c : ℕ} {δ : kˣ →* ℂˣ} {hδ : IsTame δ}
namespace GlobalTheory.TwistVertex
theorem _root_.solution (o : r ⊕ e ≃ n ⊕ Fin c)
    (x : ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).J) :
    ((parahoric r e δ hδ).toLevel.map (plainFrame o).conj).lam x = 1 := by
  rw [Level.map_lam, parahoric_lam _ 1 (by ext i; exact isEmptyElim i), map_one, map_one]
end GlobalTheory.TwistVertex
