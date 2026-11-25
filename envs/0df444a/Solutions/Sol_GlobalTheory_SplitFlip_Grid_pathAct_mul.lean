-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Grid.pathAct_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:22.918317+00:00
-- url     : https://prove2.me/submissions/8c3e012e-3f83-45c5-a3f6-f7375aaa3e3e

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
theorem _root_.solution (s : Assignment) (γ : List Edge) (g g' : G.VertexGroup) (T : G.Args → ℂ) :
    G.pathAct s γ (g * g') T = G.pathAct s γ g (G.pathAct s γ g' T) := by
  funext x
  have h1 : G.edgeFactor s (g * g') = fun e => G.edgeFactor s g e * G.edgeFactor s g' e := by
    funext e
    simp only [edgeFactor, Pi.mul_apply, map_mul, apow_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : G.moveArgs s (g * g') x = G.moveArgs s g' (G.moveArgs s g x) := by
    funext e
    simp only [moveArgs, Pi.mul_apply, map_mul, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  simp only [pathAct, h1, h2, List.prod_map_mul, mul_assoc]
end GlobalTheory.SplitFlip.Grid
