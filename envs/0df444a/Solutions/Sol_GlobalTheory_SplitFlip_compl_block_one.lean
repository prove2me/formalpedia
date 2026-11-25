-- Prove2me | solution 1 for GlobalTheory.SplitFlip.compl_block_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:15:24.574673+00:00
-- url     : https://prove2.me/submissions/98dcf0d8-3c54-45f0-8bd0-f8ed258361f9

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
variable {D₁ D₂ : Type*} [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂]
namespace GlobalTheory.SplitFlip
theorem _root_.solution : (Assignment.one.block D₁ D₂)ᶜ = Assignment.two.block D₁ D₂ := by
  ext (j | j) <;> simp [Assignment.block]
end GlobalTheory.SplitFlip
