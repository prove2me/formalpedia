-- Prove2me | solution 1 for MetricCodes.MRRW.interior_shell_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/23bb7dc8-fa77-4d02-be86-cbd2b5050afe

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_tendsto_interiorWeight_zero
import Theorems.Thm_MetricCodes_MRRW_eventually_shellRate_interior_improvement
import Theorems.Thm_MetricCodes_MRRW_eventually_interior_feasible

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∃ A b g : ℝ,
      0 < b ∧ 0 < g ∧
      MetricCodes.Johnson.Feasible δ A b g u ∧
      MetricCodes.Johnson.shellRate A b g u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hfeasible := eventually_interior_feasible
    hδ hδ' hu hua ha hboundary
  have himprovement := eventually_shellRate_interior_improvement
    (u := u) (lt_trans hu hua) ha
  have hweight := tendsto_interiorWeight_zero a u
  have hpositive :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds (lt_trans hu hua))
  have hcomplement :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < 1 - interiorWeight a u e := by
    filter_upwards
      [hweight.eventually
        (gt_mem_nhds (show a < (1 : ℝ) by linarith))]
      with e he
    linarith
  have hall : ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < interiorSupport a u e ∧
      0 < interiorComplement a u e ∧
      MetricCodes.Johnson.Feasible δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u ∧
      MetricCodes.Johnson.shellRate
          (interiorWeight a u e)
          (interiorSupport a u e)
          (interiorComplement a u e) u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
    filter_upwards [hfeasible, himprovement, hpositive, hcomplement,
      self_mem_nhdsWithin] with e hf hi hw hc (he : 0 < e)
    refine ⟨?_, ?_, hf, hi⟩
    · unfold interiorSupport
      exact mul_pos hw he
    · unfold interiorComplement
      exact mul_pos hc he
  obtain ⟨e, he⟩ := hall.exists
  exact ⟨interiorWeight a u e,
    interiorSupport a u e, interiorComplement a u e, he⟩
end MetricCodes.MRRW
