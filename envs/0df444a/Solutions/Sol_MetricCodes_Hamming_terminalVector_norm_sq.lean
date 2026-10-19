-- Prove2me | solution 1 for MetricCodes.Hamming.terminalVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/fb75b3f8-310a-4750-9e73-91706235c73f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_terminal_indicator_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution
    (k L m : ℕ) (hm : m ≤ L - k) :
    ‖terminalVector k L m‖ ^ 2 = (m : ℝ) + 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change
    (∑ p : Fin (L - k + 1),
      terminalIndicator (L - k) m p.val ^ 2) = (m : ℝ) + 1
  have hsq (p : ℕ) :
      terminalIndicator (L - k) m p ^ 2 =
        terminalIndicator (L - k) m p := by
    simp [terminalIndicator]
  simp_rw [hsq]
  rw [Fin.sum_univ_eq_sum_range]
  exact terminal_indicator_sum (L - k) m hm
end MetricCodes.Hamming
