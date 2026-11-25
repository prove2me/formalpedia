-- Prove2me | solution 1 for GroundTheory.LocalField.mem_valBall_ord_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:42.193872+00:00
-- url     : https://prove2.me/submissions/480b8a94-eb83-4e09-8862-762e7f8f6dbb

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
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
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
namespace GroundTheory.LocalField
theorem _root_.solution {c : L} (hc : c ≠ 0) {x : L} :
    x ∈ valBall L (ord c) ↔ ∃ y : 𝒪[L], x = c * y := by
  refine ⟨exists_mul_of_mem_valBall hc, ?_⟩
  rintro ⟨y, rfl⟩
  have := mul_mem_valBall (mem_valBall_ord (x := c)) (mem_valBall_zero_iff.mpr y.2)
  rwa [add_zero] at this
end GroundTheory.LocalField
