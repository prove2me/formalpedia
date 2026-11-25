-- Prove2me | solution 1 for GlobalTheory.HermForm.isIsometry_subtype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:54.161781+00:00
-- url     : https://prove2.me/submissions/1b32daf6-afcf-479c-8aa6-2d10e5da2522

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
theorem _root_.solution (h : HermForm R M) (W : Submodule R M) :
    (h.restrict W).IsIsometry h W.subtype := fun _ _ => rfl
end GlobalTheory.HermForm
