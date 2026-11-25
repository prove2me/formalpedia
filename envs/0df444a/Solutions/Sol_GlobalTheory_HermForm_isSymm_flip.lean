-- Prove2me | solution 1 for GlobalTheory.HermForm.isSymm_flip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:48:16.395096+00:00
-- url     : https://prove2.me/submissions/545da3c2-da3b-4c19-93ed-3fd87285f371

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
theorem _root_.solution : h.toSesq.flip.IsSymm := ⟨fun x y => h.star_apply y x⟩
end GlobalTheory.HermForm
