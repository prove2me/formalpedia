-- Prove2me | solution 1 for GroundTheory.LocalField.mem_valBall_algebraMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:01.104427+00:00
-- url     : https://prove2.me/submissions/1d0b1464-68a7-4560-9312-fb714bb1eebc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Theorems.Thm_GroundTheory_LocalField_algebraMap_mem_integer_iff
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
open scoped nonZeroDivisors
attribute [local instance high] FaithfulSMul.to_isTorsionFree
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution {m : ℤ} {x : L} (hx : x ∈ valBall L m) {a : K}
    (ha : a ∈ 𝒪[K]) : algebraMap K L a * x ∈ valBall L m := by
  have := mul_mem_valBall (mem_valBall_zero_iff.mpr ((algebraMap_mem_integer_iff K L a).mpr ha)) hx
  rwa [zero_add] at this
end GroundTheory.LocalField
