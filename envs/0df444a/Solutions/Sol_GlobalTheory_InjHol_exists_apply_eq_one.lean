-- Prove2me | solution 1 for GlobalTheory.InjHol.exists_apply_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:26.290306+00:00
-- url     : https://prove2.me/submissions/81142321-bf65-4901-acb0-7c32d91e4439

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AnalyticAtEntry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotInjOnOfFderivEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Metric Topology
open scoped ContDiff
open GlobalTheory GlobalTheory.InjHol
namespace GlobalTheory.InjHol
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {L : E →L[ℂ] ℂ} (h : L ≠ 0) : ∃ v, L v = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, L w ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (ContinuousLinearMap.ext hc)
  exact ⟨(L w)⁻¹ • w, by simp [hw]⟩
end GlobalTheory.InjHol
