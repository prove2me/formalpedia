-- Prove2me | solution 1 for GlobalTheory.SplitFlip.Grid.exists_isGood
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:09:35.3207+00:00
-- url     : https://prove2.me/submissions/8dea202d-29ff-4b33-b421-e20af407871e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Theorems.Thm_GlobalTheory_SplitFlip_exists_localSetting

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
theorem _root_.solution (m r t s : ℕ) (ht : Odd t) (hs : Odd s) : ∃ (G : Grid k) (ϖ : kˣ) (ψ : AddChar k Circle),
    G.m = m ∧ G.r = r ∧ G.t = t ∧ G.s = s ∧ G.IsGood ϖ ψ 2 := by
  obtain ⟨ϖ, ψ, α, h⟩ := exists_localSetting (k := k)
  exact ⟨⟨m, r, t, s, fun _ => α, fun _ => 1, 1⟩, ϖ, ψ, rfl, rfl, rfl, rfl, ht, hs, fun _ _ => rfl,
    fun i _ j _ => by simpa [alpha, beta] using h⟩
end GlobalTheory.SplitFlip.Grid
