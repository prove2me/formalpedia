-- Prove2me | solution 1 for GlobalTheory.ExplicitRect.eq_add_dslope
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:32.781327+00:00
-- url     : https://prove2.me/submissions/2bcde413-5e57-4c88-9e86-9b395c15226a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AnalyticAtDslope

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.ExplicitRect
namespace GlobalTheory.ExplicitRect
theorem _root_.solution (f : ℂ → ℂ) (p s : ℂ) : f s = f p + (s - p) * dslope f p s := by
  have h := sub_smul_dslope f p s
  rw [smul_eq_mul] at h
  linear_combination -h
end GlobalTheory.ExplicitRect
