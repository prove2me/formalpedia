-- Prove2me | solution 1 for GroundTheory.LocalField.partialNorm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:20.485803+00:00
-- url     : https://prove2.me/submissions/554ef76b-27db-4952-81a3-46a66cf6e581

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (σ : L ≃ₐ[K] L) (x : Lˣ)
omit [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution : partialNorm σ x 1 = x := by
  rw [partialNorm, prod_range_one, pow_zero, one_smul]
end GroundTheory.LocalField
