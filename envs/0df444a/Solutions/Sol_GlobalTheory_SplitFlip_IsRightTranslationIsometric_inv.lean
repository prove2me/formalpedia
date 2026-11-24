-- Prove2me | solution 1 for GlobalTheory.SplitFlip.IsRightTranslationIsometric.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:46.014648+00:00
-- url     : https://prove2.me/submissions/56dd5944-3acc-47c2-83b6-dfaad31fde33

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
namespace IsRightTranslationIsometric
theorem _root_.solution {ϖ : kˣ} {ψ : AddChar k Circle} {α β : kˣ →* ℂˣ} {e : ℕ} (h : IsRightTranslationIsometric ϖ ψ α β e) :
    IsRightTranslationIsometric ϖ ψ⁻¹ α β e :=
  { h with cond := fun x => by simpa only [AddChar.inv_apply', inv_eq_one] using h.cond x }
end IsRightTranslationIsometric
end GlobalTheory.SplitFlip
