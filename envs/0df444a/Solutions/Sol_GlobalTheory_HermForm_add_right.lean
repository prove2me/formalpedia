-- Prove2me | solution 1 for GlobalTheory.HermForm.add_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:53:15.756419+00:00
-- url     : https://prove2.me/submissions/f922e9f7-6a35-4a6c-a17f-31177046a8aa

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
theorem _root_.solution (x y z : M) : h x (y + z) = h x y + h x z := by simp
end GlobalTheory.HermForm
