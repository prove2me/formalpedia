-- Prove2me | solution 1 for GlobalTheory.SplitFlip.CondLE.div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:54:09.597306+00:00
-- url     : https://prove2.me/submissions/c26800b7-e74a-4f06-8614-d52c1a9cb1b8

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
namespace CondLE
theorem _root_.solution {ϖ : kˣ} {e : ℕ} {α β : kˣ →* ℂˣ} (hα : CondLE ϖ e α) (hβ : CondLE ϖ e β) :
    CondLE ϖ e (α / β) := fun x hx => by simp [hα x hx, hβ x hx]
end CondLE
end GlobalTheory.SplitFlip
