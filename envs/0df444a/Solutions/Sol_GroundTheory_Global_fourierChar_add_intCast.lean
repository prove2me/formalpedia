-- Prove2me | solution 1 for GroundTheory.Global.fourierChar_add_intCast
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:31:02.228144+00:00
-- url     : https://prove2.me/submissions/dcff34f0-1114-4bf0-b028-c09460cb1264

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoissonBasic
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LatticePoisson

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
open MeasureTheory Module Set Filter Topology
open scoped RealInnerProductSpace FourierTransform SchwartzMap
noncomputable section
namespace GroundTheory.Global
theorem _root_.solution (x : ℝ) (k : ℤ) : 𝐞 (x + k) = 𝐞 x := by
  rw [AddChar.map_add_eq_mul]
  have : 𝐞 (k : ℝ) = 1 := by
    ext
    rw [Real.fourierChar_apply, Circle.coe_one]
    convert Complex.exp_int_mul_two_pi_mul_I k using 2
    push_cast
    ring
  rw [this, mul_one]
end GroundTheory.Global
