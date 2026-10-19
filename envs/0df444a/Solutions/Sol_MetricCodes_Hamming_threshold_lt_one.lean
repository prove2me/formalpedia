-- Prove2me | solution 1 for MetricCodes.Hamming.threshold_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/d0ca94b7-2bfc-4401-96dc-a520966f65ec

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    threshold n d < 1 := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold threshold
  have hpos : 0 < 2 * (d : ℝ) / (n : ℝ) := by positivity
  linarith
end MetricCodes.Hamming
