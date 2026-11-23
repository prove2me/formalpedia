-- Prove2me | solution 1 for GlobalTheory.LineCos.lineVec_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:51.476314+00:00
-- url     : https://prove2.me/submissions/741c805f-bfcf-44ed-80f3-dacca7ae9a1e

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOnCosSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Set Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LineCos
namespace GlobalTheory.LineCos
theorem _root_.solution (s : Bool) (x : ℂ) : lineVec s x ≠ 0 := by
  intro h
  cases s
  · simpa [lineVec] using congrFun h 0
  · simpa [lineVec] using congrFun h 1
end GlobalTheory.LineCos
