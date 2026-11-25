-- Prove2me | solution 1 for GlobalTheory.HermForm.unitaryGroup.smul_app_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:50:45.099902+00:00
-- url     : https://prove2.me/submissions/e91597c7-665f-4277-8bc3-c25ce66cdb74

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
open GlobalTheory.HermForm.unitaryGroup
namespace GlobalTheory.HermForm.unitaryGroup
theorem _root_.solution (g : h.unitaryGroup) (x y : M) : h x (g • y) = h (g⁻¹ • x) y := by
  rw [← smul_app g _ y, smul_inv_smul]
end GlobalTheory.HermForm.unitaryGroup
