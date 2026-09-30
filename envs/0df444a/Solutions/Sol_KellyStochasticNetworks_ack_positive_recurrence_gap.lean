-- Prove2me | solution 1 for KellyStochasticNetworks.ack_positive_recurrence_gap
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:18:53.864028+00:00
-- url     : https://prove2.me/submissions/53680b40-b2c7-43e2-9565-8361f41bda1a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_RandomAccess

namespace KellyStochasticNetworks

theorem ra_gap :
    (∀ ν : ℝ, 0 < ν → ν ≤ Real.exp (-ν) → ν < 0.5672)
      ∧ (0.5672 : ℝ) < Real.log 2 := by
  refine ⟨fun ν hν h => ?_, lt_trans (by norm_num) Real.log_two_gt_d9⟩
  by_contra hc
  push Not at hc
  have h1 : Real.exp (-ν) ≤ Real.exp (-0.5672) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-0.5672 : ℝ) < 0.5672 := by
    have hs := Real.sum_le_exp_of_nonneg (x := (0.5672:ℝ)) (by norm_num) 6
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hs
    norm_num at hs
    have hpos := Real.exp_pos (0.5672:ℝ)
    rw [Real.exp_neg, inv_lt_comm₀ hpos (by norm_num)]
    calc (0.5672:ℝ)⁻¹ < 1.7632 := by norm_num
      _ ≤ Real.exp 0.5672 := by linarith
  linarith

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution :
    (∀ ν : ℝ, 0 < ν → ν ≤ Real.exp (-ν) → ν < 0.5672)
      ∧ (0.5672 : ℝ) < Real.log 2 := by
  exact ra_gap
