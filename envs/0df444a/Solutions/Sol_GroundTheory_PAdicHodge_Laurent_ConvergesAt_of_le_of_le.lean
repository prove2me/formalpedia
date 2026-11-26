-- Prove2me | solution 1 for GroundTheory.PAdicHodge.Laurent.ConvergesAt.of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T14:41:21.388573+00:00
-- url     : https://prove2.me/submissions/3382e1fd-700c-4313-84bb-28dfca678a0e

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_RobbaSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology
open GroundTheory.PAdicHodge.Laurent
set_option linter.unusedSectionVars false
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {a b c : ℤ → K} {ρ : ℝ}

theorem solution {ρ₁ ρ₂ : ℝ} (h₁ : ConvergesAt a ρ₁) (h₂ : ConvergesAt a ρ₂)
    (hρ₁ : 0 < ρ₁) (h1 : ρ₁ ≤ ρ) (h2 : ρ ≤ ρ₂) : ConvergesAt a ρ := by
  have hρ : 0 < ρ := hρ₁.trans_le h1
  have hρ₂ : 0 < ρ₂ := hρ.trans_le h2
  unfold ConvergesAt at *
  refine Metric.tendsto_nhds.mpr fun ε εpos => ?_
  have ev₁ := (Metric.tendsto_nhds.mp h₁) ε εpos
  have ev₂ := (Metric.tendsto_nhds.mp h₂) ε εpos
  filter_upwards [ev₁, ev₂] with n hn₁ hn₂
  have h0 : 0 ≤ ‖a n‖ * ρ ^ n := mul_nonneg (norm_nonneg _) (zpow_nonneg hρ.le n)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  by_cases hn : 0 ≤ n
  · refine lt_of_le_of_lt ?_ (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (zpow_nonneg hρ₂.le n))] at hn₂
      exact hn₂)
    exact mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ hn hρ.le h2) (norm_nonneg _)
  · have hn' : n ≤ 0 := le_of_not_ge hn
    refine lt_of_le_of_lt ?_ (by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg
        (mul_nonneg (norm_nonneg _) (zpow_nonneg hρ₁.le n))] at hn₁
      exact hn₁)
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hnneg : 0 ≤ -n := neg_nonneg.mpr hn'
    have hρn : ρ ^ n = (ρ⁻¹) ^ (-n) := by rw [zpow_neg, inv_zpow, inv_inv]
    have hρ₁n : ρ₁ ^ n = (ρ₁⁻¹) ^ (-n) := by rw [zpow_neg, inv_zpow, inv_inv]
    rw [hρn, hρ₁n]
    exact zpow_le_zpow_left₀ hnneg (inv_nonneg.mpr hρ.le) ((inv_le_inv₀ hρ hρ₁).mpr h1)
