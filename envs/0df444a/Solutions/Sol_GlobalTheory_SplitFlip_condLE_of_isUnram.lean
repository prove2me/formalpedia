-- Prove2me | solution 1 for GlobalTheory.SplitFlip.condLE_of_isUnram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:15:31.565729+00:00
-- url     : https://prove2.me/submissions/ee4da795-cc82-4377-9754-f7d0aae1aa4f

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
namespace GlobalTheory.SplitFlip
theorem _root_.solution (ϖ : kˣ) (e : ℕ) {χ : kˣ →* ℂˣ} (h : IsUnram χ) : CondLE ϖ e χ :=
  fun x hx => h x hx.1
end GlobalTheory.SplitFlip
