-- Prove2me | solution 1 for MetricCodes.choose_monotone_to_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.340887+00:00
-- url     : https://prove2.me/submissions/be098e4a-1d62-4872-8a7d-84ef67e3271f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_sum_booleanHarmonicDimension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open scoped BigOperators
open Finset
namespace MetricCodes
theorem _root_.solution (n : ℕ) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n / 2) :
    n.choose i ≤ n.choose j := by
  have hi : 2 * i ≤ n := by omega
  have hj' : 2 * j ≤ n := by omega
  rw [← sum_booleanHarmonicDimension n i hi,
    ← sum_booleanHarmonicDimension n j hj']
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
end MetricCodes
