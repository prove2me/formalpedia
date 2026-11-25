-- Prove2me | solution 1 for GlobalTheory.HermForm.Nondegenerate.ext_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:46:46.806065+00:00
-- url     : https://prove2.me/submissions/f8928bfc-7bd5-4d71-9edb-86b657e14b04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_HermForm_sub_left

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
theorem _root_.solution (H : h.Nondegenerate) {x x' : M} (hx : ∀ y, h x y = h x' y) :
    x = x' :=
  sub_eq_zero.1 (H.eq_zero_left fun y => by rw [sub_left, hx, sub_self])
end Nondegenerate
end GlobalTheory.HermForm
