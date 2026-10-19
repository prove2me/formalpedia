-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalEntropy_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/814dbc5c-e6d7-4b05-901b-59c553a8326a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution : Continuous MetricCodes.sphericalEntropy := by
  have hplus :
      Continuous (fun u : ℝ => (1 + u) * Real.log (1 + u)) := by
    simpa [Function.comp_def, Pi.add_apply] using
      (Real.continuous_mul_log.comp
        (continuous_const.add continuous_id :
          Continuous (fun u : ℝ => 1 + u)))
  have hnatural : Continuous
      (fun u : ℝ =>
        ((1 + u) * Real.log (1 + u) - u * Real.log u) /
          Real.log 2) :=
    (hplus.sub Real.continuous_mul_log).div_const (Real.log 2)
  convert hnatural using 1
  funext u
  unfold MetricCodes.sphericalEntropy Real.logb
  ring
end MetricCodes.Spherical
