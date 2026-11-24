-- Prove2me | solution 1 for GlobalTheory.SplitFlip.exists_localSetting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:54:57.038853+00:00
-- url     : https://prove2.me/submissions/c63668b3-7aff-4d4a-8db2-1f513090995b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_exists_isUnif
import Theorems.Thm_GlobalTheory_SplitFlip_exists_ramified
import Theorems.Thm_GlobalTheory_SplitWeil_Model_exists_hasConductor


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
theorem _root_.solution : ∃ (ϖ : kˣ) (ψ : AddChar k Circle) (α : kˣ →* ℂˣ), IsRightTranslationIsometric ϖ ψ α 1 2 := by
  obtain ⟨ϖ, hϖ⟩ := exists_isUnif (k := k)
  obtain ⟨ψ, hψ⟩ := exists_hasConductor (k := k)
  obtain ⟨ν, h1, h2, h3⟩ := exists_ramified hϖ
  exact ⟨ϖ, ψ, ν, hϖ, hψ, by simpa using h1, by simpa using h3, one_le_two, h2, fun _ _ => rfl⟩
end GlobalTheory.SplitFlip
