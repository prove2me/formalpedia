-- Prove2me | solution 1 for GroundTheory.Global.realGaussian_eq_ofReal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:48:32.110269+00:00
-- url     : https://prove2.me/submissions/a560e328-9ad8-4c71-aa01-871e6605f5b5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Complex MeasureTheory Set Real
open scoped FourierTransform
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (x : ℝ) :
    realGaussian x = ((Real.exp (-(π * x ^ 2)) : ℝ) : ℂ) := by
  simp [realGaussian, ofReal_exp]
end GroundTheory.Global
