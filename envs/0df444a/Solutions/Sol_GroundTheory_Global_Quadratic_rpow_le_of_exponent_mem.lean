-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.rpow_le_of_exponent_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:02.941487+00:00
-- url     : https://prove2.me/submissions/16b53c8a-e9ac-49c2-866b-f7fb1ea000da

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution {b c e : ℝ} (hc : 0 < c) (hcb : c ≤ b) (he1 : -(9 / 2) ≤ e)
    (he2 : e ≤ -(3 / 2)) : b ^ e ≤ c ^ (-(3 / 2) : ℝ) + c ^ (-(9 / 2) : ℝ) := by
  have hb : 0 < b := hc.trans_le hcb
  have h1 : 0 ≤ c ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg hc.le _
  have h2 : 0 ≤ c ^ (-(9 / 2) : ℝ) := Real.rpow_nonneg hc.le _
  rcases le_or_gt 1 b with hb1 | hb1
  · calc b ^ e ≤ b ^ (-(3 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_le hb1 he2
      _ ≤ c ^ (-(3 / 2) : ℝ) := Real.rpow_le_rpow_of_nonpos hc hcb (by norm_num)
      _ ≤ _ := le_add_of_nonneg_right h2
  · calc b ^ e ≤ b ^ (-(9 / 2) : ℝ) := Real.rpow_le_rpow_of_exponent_ge hb hb1.le he1
      _ ≤ c ^ (-(9 / 2) : ℝ) := Real.rpow_le_rpow_of_nonpos hc hcb (by norm_num)
      _ ≤ _ := le_add_of_nonneg_left h1
end GroundTheory.Global.Quadratic
