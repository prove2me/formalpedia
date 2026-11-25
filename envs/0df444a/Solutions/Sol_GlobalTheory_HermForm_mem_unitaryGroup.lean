-- Prove2me | solution 1 for GlobalTheory.HermForm.mem_unitaryGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:48:19.421154+00:00
-- url     : https://prove2.me/submissions/1996b2e5-df1c-43c3-9733-20abe5d9afec

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
theorem _root_.solution {g : M ≃ₗ[R] M} :
    g ∈ h.unitaryGroup ↔ ∀ x y, h (g x) (g y) = h x y := Iff.rfl
end GlobalTheory.HermForm
