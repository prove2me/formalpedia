-- Prove2me | solution 1 for GlobalTheory.HermForm.isSelfAdjoint_apply_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:48:13.362811+00:00
-- url     : https://prove2.me/submissions/7ee2168e-17dc-4b5a-a8af-c6d74a8abc0a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
open GlobalTheory.HermForm
variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
variable (h : HermForm R M)
namespace GlobalTheory.HermForm
theorem _root_.solution (x : M) : IsSelfAdjoint (h x x) := h.star_apply x x
end GlobalTheory.HermForm
