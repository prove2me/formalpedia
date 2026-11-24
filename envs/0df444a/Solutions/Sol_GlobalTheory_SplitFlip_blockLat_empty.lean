-- Prove2me | solution 1 for GlobalTheory.SplitFlip.blockLat_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:55.484877+00:00
-- url     : https://prove2.me/submissions/d5f95a2a-3bf6-4e6d-b0ed-3d0b9c3bd329

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
variable {A D : Type*}
variable [Fintype D]
variable [DecidableEq D]
omit [Fintype D]
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ϖ : kˣ) (e : ℕ) : blockLat ϖ e (∅ : Finset D) = stdLat k D := by
  unfold blockLat stdLat; congr 1
end GlobalTheory.SplitFlip
