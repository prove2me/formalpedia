-- Prove2me | solution 1 for GlobalTheory.HermForm.isIsometry_iff_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:49:50.071521+00:00
-- url     : https://prove2.me/submissions/ed21342d-2ccb-4b35-9a84-ddb08529fabd

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
theorem _root_.solution {h₁ : HermForm R M} {h₂ : HermForm R N} {f : M →ₗ[R] N} :
    h₁.IsIsometry h₂ f ↔ h₂.comap f = h₁ :=
  ⟨fun H => ext H, fun H x y => by rw [← H]; rfl⟩
end GlobalTheory.HermForm
