-- Prove2me | solution 1 for MetricCodes.Spherical.variationalRate_le_of_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/46cee4a7-39e9-413c-8d7e-861b4df323ab

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_rateSet_bddBelow
import Theorems.Thm_MetricCodes_Johnson_rateSet_bddBelow
import Theorems.Thm_MetricCodes_Spherical_rateSet_bddBelow

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution {s a b : ℝ}
    (h : Feasible s a b) :
    variationalRate s ≤
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  exact csInf_le (rateSet_bddBelow s) ⟨a, b, h, rfl⟩
end MetricCodes.Spherical
