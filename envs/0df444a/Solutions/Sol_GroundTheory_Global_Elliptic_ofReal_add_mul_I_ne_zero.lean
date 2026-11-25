-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.ofReal_add_mul_I_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:18.110298+00:00
-- url     : https://prove2.me/submissions/5ab6f22b-6daa-49b3-b91b-ddba22ee4001

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {c : ℝ} (hc : c ≠ 0) (x : ℝ) : (x : ℂ) + c * I ≠ 0 := by
  intro h
  apply hc
  simpa using congrArg Complex.im h
end GroundTheory.Global.Elliptic
