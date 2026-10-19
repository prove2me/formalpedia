-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalEntropy_sub_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/94040f2b-c248-4990-ae23-b1e858405747

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_strictMono

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) :
    0 ≤ MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  have ha : 0 ≤ a := hb.trans hba
  exact sub_nonneg.mpr
    (sphericalEntropy_strictMono.monotoneOn hb ha hba)
end MetricCodes.Spherical
