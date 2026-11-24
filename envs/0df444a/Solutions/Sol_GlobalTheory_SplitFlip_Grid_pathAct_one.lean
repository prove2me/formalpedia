-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Grid.pathAct_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:54:56.355225+00:00
-- url     : https://prove2.me/submissions/05bb837e-2685-4817-8101-9c4965052062

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitFlip
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
open GlobalTheory.SplitFlip.Grid
variable (G : Grid k)
namespace GlobalTheory.SplitFlip.Grid
theorem _root_.solution (s : Assignment) (γ : List Edge) (T : G.Args → ℂ) : G.pathAct s γ 1 T = T := by
  funext x
  have h1 : G.edgeFactor s 1 = fun _ => 1 := by funext e; simp [edgeFactor]
  have h2 : G.moveArgs s 1 x = x := by funext e; simp [moveArgs]
  simp [pathAct, h1, h2]
end GlobalTheory.SplitFlip.Grid
