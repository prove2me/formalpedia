-- Prove2me | solution 1 for GlobalTheory.HermForm.Nondegenerate.eq_zero_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:52.564713+00:00
-- url     : https://prove2.me/submissions/66b8f4e8-d37c-4d6b-ac30-204383f44f50

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
variable {h}
namespace GlobalTheory.HermForm
namespace Nondegenerate
theorem _root_.solution (H : h.Nondegenerate) {y : M} (hy : ∀ x, h x y = 0) : y = 0 :=
  H.2 y hy
end Nondegenerate
end GlobalTheory.HermForm
