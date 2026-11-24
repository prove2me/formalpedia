-- Prove2me | solution 1 for GlobalTheory.TopForm.IsFreeGen.unit_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:53.34119+00:00
-- url     : https://prove2.me/submissions/6ffac629-fded-4099-beb2-d7dd1f557086

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {ω : M}
namespace GlobalTheory.TopForm
namespace IsFreeGen
theorem _root_.solution (h : IsFreeGen A ω) (u : Aˣ) : IsFreeGen A ((u : A) • ω) := by
  have : (fun a : A => a • (u : A) • ω) = (fun a : A => a • ω) ∘ (· * (u : A)) := by
    funext a
    exact (mul_smul _ _ _).symm
  rw [IsFreeGen, this]
  exact h.comp u.mulRight.bijective
end IsFreeGen
end GlobalTheory.TopForm
