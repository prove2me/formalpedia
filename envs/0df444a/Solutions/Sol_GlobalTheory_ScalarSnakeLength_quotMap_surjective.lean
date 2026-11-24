-- Prove2me | solution 1 for GlobalTheory.ScalarSnakeLength.quotMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:35:48.060858+00:00
-- url     : https://prove2.me/submissions/4c22f70a-e28b-4614-ab0a-3605731db214

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LengthEqKerAddRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.ScalarSnakeLength
variable {A : Type} [CommRing A]
variable {M₁ M₂ M₃ : Type} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module A M₁] [Module A M₂] [Module A M₃]
namespace GlobalTheory.ScalarSnakeLength
theorem _root_.solution (g : M₂ →ₗ[A] M₃) (hg : Function.Surjective g) (b : A) :
    Function.Surjective (quotMap g b) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  obtain ⟨y, rfl⟩ := hg x
  exact ⟨(LinearMap.range (LinearMap.lsmul A M₂ b)).mkQ y, rfl⟩
end GlobalTheory.ScalarSnakeLength
