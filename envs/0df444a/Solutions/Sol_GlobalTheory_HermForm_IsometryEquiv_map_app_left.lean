-- Prove2me | solution 1 for GlobalTheory.HermForm.IsometryEquiv.map_app_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:46:42.470107+00:00
-- url     : https://prove2.me/submissions/fa0cc203-a293-4e43-a2fb-dee9980a6374

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
open GlobalTheory.HermForm.IsometryEquiv
variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}
namespace GlobalTheory.HermForm.IsometryEquiv
theorem _root_.solution (f : h₁.IsometryEquiv h₂) (x : M) (y : N) :
    h₂ (f x) y = h₁ x (f.symm y) := by rw [← f.map_app, apply_symm_apply]
end GlobalTheory.HermForm.IsometryEquiv
