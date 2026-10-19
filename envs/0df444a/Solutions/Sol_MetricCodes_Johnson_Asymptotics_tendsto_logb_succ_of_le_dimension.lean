-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_logb_succ_of_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/0a47a629-168a-4a25-bc63-07e677ebba2f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_succ_div

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution
    {N : ℕ → ℕ}
    (hN : ∀ᶠ n : ℕ in atTop, N n ≤ n) :
    Tendsto
      (fun n : ℕ => Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hupper := MetricCodes.Hamming.tendsto_logb_succ_div
  have hnonnegative :
      ∀ᶠ n : ℕ in atTop,
        (0 : ℝ) ≤
          Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply div_nonneg
    · apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
      exact_mod_cast (show 1 ≤ N n + 1 by omega)
    · exact Nat.cast_nonneg n
  have hbounded :
      ∀ᶠ n : ℕ in atTop,
        Real.logb 2 ((N n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [hN, eventually_gt_atTop (0 : ℕ)]
      with n hNn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).mpr
    apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    · exact_mod_cast (show 0 < N n + 1 by omega)
    · exact_mod_cast (show N n + 1 ≤ n + 1 by omega)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hzero hupper hnonnegative hbounded
end MetricCodes.Johnson.Asymptotics
