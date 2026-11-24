-- Prove2me | solution 1 for GlobalTheory.HermForm.Nondegenerate.ext_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:45:46.038223+00:00
-- url     : https://prove2.me/submissions/2326bd16-5591-489d-8bce-34b5bcd15f11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_HermForm_sub_right
import Theorems.Thm_GlobalTheory_HermForm_Nondegenerate_eq_zero_right

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
theorem _root_.solution (H : h.Nondegenerate) {y y' : M} (hy : ∀ x, h x y = h x y') :
    y = y' :=
  sub_eq_zero.1 (H.eq_zero_right fun x => by rw [sub_right, hy, sub_self])
end Nondegenerate
end GlobalTheory.HermForm
