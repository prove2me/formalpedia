-- Prove2me | solution 1 for GlobalTheory.InjHol.exists_zero_of_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:52.671318+00:00
-- url     : https://prove2.me/submissions/11c8ad94-3c85-4db2-94ed-2266179c2213

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
theorem _root_.solution {φ : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hφ : DifferentiableOn ℂ φ (closedBall c r)) (h : ∀ t ∈ sphere c r, ‖φ c‖ < ‖φ t‖) :
    ∃ t ∈ closedBall c r, φ t = 0 := by
  by_contra hne
  push Not at hne
  have hd : DiffContOnCl ℂ (fun t => (φ t)⁻¹) (ball c r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hr.ne']
    exact hφ.inv hne
  obtain ⟨t, ht, hmax⟩ := Complex.exists_mem_frontier_isMaxOn_norm isBounded_ball
    (nonempty_ball.mpr hr) hd
  rw [frontier_ball c hr.ne'] at ht
  have h1 : ‖(φ c)⁻¹‖ ≤ ‖(φ t)⁻¹‖ := hmax (subset_closure (mem_ball_self hr))
  rw [norm_inv, norm_inv] at h1
  have h2 : 0 < ‖φ c‖ := norm_pos_iff.mpr (hne c (mem_closedBall_self hr.le))
  exact absurd (inv_strictAnti₀ h2 (h t ht)) (not_lt.mpr h1)
end GlobalTheory.InjHol
