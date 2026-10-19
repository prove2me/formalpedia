-- Prove2me | solution 1 for MetricCodes.Johnson.mrrwG_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/c7b8131c-f0e7-4ee3-868f-2e0bf365ba71

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_binaryEntropy_continuous

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
open scoped BigOperators InnerProductSpace Matrix
namespace MetricCodes.Johnson
theorem _root_.solution : Continuous mrrwG := by
  unfold mrrwG
  exact MetricCodes.Hamming.binaryEntropy_continuous.comp
    ((continuous_const.sub
      ((continuous_const.sub continuous_id).sqrt)).div_const 2)
end MetricCodes.Johnson
