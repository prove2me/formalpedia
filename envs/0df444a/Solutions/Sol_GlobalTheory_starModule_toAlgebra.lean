-- Prove2me | solution 1 for GlobalTheory.starModule_toAlgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:41:48.520906+00:00
-- url     : https://prove2.me/submissions/41a8b15d-c8ae-4e8a-82cd-bf405d5eef14

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
universe u v
attribute [instance] HermModule.addCommGroup HermModule.module
attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite
attribute [simp] IsStarFixed.star_algebraMap
namespace GlobalTheory
theorem _root_.solution {R S : Type*} [CommSemiring R] [CommSemiring S] [StarRing R]
    [StarRing S] (φ : R →+* S) (hφ : ∀ x, φ (star x) = star (φ x)) :
    letI := φ.toAlgebra
    StarModule R S :=
  letI := φ.toAlgebra
  ⟨fun r s => by
    change star (φ r * s) = φ (star r) * star s
    rw [star_mul', hφ]⟩
end GlobalTheory
