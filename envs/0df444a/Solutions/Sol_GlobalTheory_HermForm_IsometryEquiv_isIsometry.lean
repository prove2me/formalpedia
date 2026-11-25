-- Prove2me | solution 1 for GlobalTheory.HermForm.IsometryEquiv.isIsometry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:46:37.64495+00:00
-- url     : https://prove2.me/submissions/19c2ad02-8ab0-48d7-ad66-e6de688195f3

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
theorem _root_.solution (f : h₁.IsometryEquiv h₂) : h₁.IsIsometry h₂ f.toLinearEquiv.toLinearMap :=
  f.map_app'
end GlobalTheory.HermForm.IsometryEquiv
