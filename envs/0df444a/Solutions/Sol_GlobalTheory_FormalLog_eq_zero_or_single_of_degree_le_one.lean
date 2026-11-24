-- Prove2me | solution 1 for GlobalTheory.FormalLog.eq_zero_or_single_of_degree_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:27:11.966074+00:00
-- url     : https://prove2.me/submissions/0f4f8869-a82f-488d-9305-2d892ff70c5b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_FormalCompApplyEqMvPowerSeriesSubst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PderivSecondEvFirstPointEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EqZeroOrSingleOfDegreeLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.FormalLog
namespace GlobalTheory.FormalLog
theorem _root_.solution {σ : Type} (μ : σ →₀ ℕ) (h : μ.degree ≤ 1) :
    μ = 0 ∨ ∃ s, μ = Finsupp.single s 1 := by
  classical
  by_cases h0 : μ = 0
  · exact Or.inl h0
  · right
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 h0
    have hs' : 1 ≤ μ s := Nat.one_le_iff_ne_zero.2 hs
    have hle : Finsupp.single s 1 ≤ μ := Finsupp.single_le_iff.2 hs'
    obtain ⟨ν, rfl⟩ := exists_add_of_le hle
    rw [map_add, Finsupp.degree_single] at h
    have : ν = 0 := (Finsupp.degree_eq_zero_iff ν).1 (by omega)
    exact ⟨s, by rw [this, add_zero]⟩
end GlobalTheory.FormalLog
