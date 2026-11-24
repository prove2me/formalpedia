-- Prove2me | solution 1 for GlobalTheory.OrbitGrowth.le_grow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:17:16.95582+00:00
-- url     : https://prove2.me/submissions/eb44694a-1400-4578-87ad-18e7f18cad8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_MulApply
import Theorems.Thm_GlobalTheory_OrbitGrowth_mem_grow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.OrbitGrowth
variable {M : Type} [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.OrbitGrowth
theorem _root_.solution (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : W ≤ grow A W := by
  intro x hx
  have := mem_grow A.one_mem hx
  simpa using this
end GlobalTheory.OrbitGrowth
