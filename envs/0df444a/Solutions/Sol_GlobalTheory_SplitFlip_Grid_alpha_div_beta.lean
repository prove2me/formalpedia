-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Grid.alpha_div_beta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:12:08.538445+00:00
-- url     : https://prove2.me/submissions/6e3309cb-5636-4a12-ac1d-55c30fca44ac

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
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitFlip.Grid
theorem _root_.solution (i j : ℕ) : G.alpha i j / G.beta i j = G.nu i j := mul_div_mul_right_eq_div _ _ _
end GlobalTheory.SplitFlip.Grid
