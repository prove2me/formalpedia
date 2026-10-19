-- Prove2me | solution 1 for MetricCodes.Johnson.bassalygo_elias_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/128fc041-07ba-4957-96b6-175597782dce

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_bassalygo_elias

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution {n w d : ℕ} (hw : w ≤ n) :
    (binaryCodeNumber n d : ℝ) ≤
      ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (shellCodeNumber n w d : ℝ) := by
  have hc : 0 < (n.choose w : ℝ) := by
    exact_mod_cast Nat.choose_pos hw
  calc
    (binaryCodeNumber n d : ℝ) ≤
        ((2 : ℝ) ^ n * (shellCodeNumber n w d : ℝ)) /
          (n.choose w : ℝ) := by
      apply (le_div_iff₀ hc).mpr
      exact_mod_cast bassalygo_elias n w d
    _ = ((2 : ℝ) ^ n / (n.choose w : ℝ)) *
        (shellCodeNumber n w d : ℝ) := by
      ring
end MetricCodes.Johnson
