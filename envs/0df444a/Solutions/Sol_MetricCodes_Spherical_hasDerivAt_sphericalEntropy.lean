-- Prove2me | solution 1 for MetricCodes.Spherical.hasDerivAt_sphericalEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/3fe4bc95-3ae4-4675-92d8-5efdf7296e8a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution {u : ℝ} (hu : 0 < u) :
    HasDerivAt MetricCodes.sphericalEntropy
      (Real.logb 2 ((1 + u) / u)) u := by
  have hplus :=
    (Real.hasDerivAt_mul_log (by linarith : 1 + u ≠ 0)).comp u
      ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u))
  have hself := Real.hasDerivAt_mul_log hu.ne'
  have hderiv := (hplus.sub hself).div_const (Real.log 2)
  have hfun : MetricCodes.sphericalEntropy =
      (fun x : ℝ =>
        ((1 + x) * Real.log (1 + x) - x * Real.log x) /
          Real.log 2) := by
    funext x
    unfold MetricCodes.sphericalEntropy Real.logb
    ring
  have hvalue :
      Real.logb 2 ((1 + u) / u) =
        (((Real.log (1 + u) + 1) * (0 + 1) -
          (Real.log u + 1)) / Real.log 2) := by
    unfold Real.logb
    rw [Real.log_div (by linarith : 1 + u ≠ 0) hu.ne']
    ring
  rw [hfun, hvalue]
  simpa only [Function.comp_apply, Pi.sub_apply] using hderiv
end MetricCodes.Spherical
