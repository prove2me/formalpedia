-- Prove2me | solution 1 for MetricCodes.hammingCorrelation_le_of_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.096655+00:00
-- url     : https://prove2.me/submissions/696c63ec-2e30-4e6a-a59a-7a1795184356

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators InnerProductSpace
namespace MetricCodes
theorem _root_.solution
    {n d : ℕ} (hn : 0 < n) {x y : BinaryWord n}
    (hd : d ≤ hammingDist x y) :
    hammingCorrelation x y ≤ 1 - 2 * (d : ℝ) / (n : ℝ) := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hd' : (d : ℝ) ≤ (hammingDist x y : ℝ) := by
    exact_mod_cast hd
  unfold hammingCorrelation
  have hdiv :
      2 * (d : ℝ) / (n : ℝ) ≤
        2 * (hammingDist x y : ℝ) / (n : ℝ) := by
    exact (div_le_div_iff_of_pos_right hn').2 (by linarith)
  linarith
end MetricCodes
