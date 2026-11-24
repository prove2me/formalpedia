-- Prove2me | solution 1 for GlobalTheory.relLength_map_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:19.205507+00:00
-- url     : https://prove2.me/submissions/4a432623-be7d-43b8-8f75-0be587953b4a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R S V V' : Type*} [Ring R] [Ring S] [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} [RingHomSurjective σ]
namespace GlobalTheory
theorem _root_.solution (f : V →ₛₗ[σ] V') (A B : Submodule R V) :
    relLength (A.map f) (B.map f) = relLength A (B ⊔ LinearMap.ker f) := by
  rw [relLength_map_left, Submodule.comap_map_eq]
end GlobalTheory
