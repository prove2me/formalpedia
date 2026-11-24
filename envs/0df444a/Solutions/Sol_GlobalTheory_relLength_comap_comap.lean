-- Prove2me | solution 1 for GlobalTheory.relLength_comap_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:17.512811+00:00
-- url     : https://prove2.me/submissions/7c302399-6726-445c-b7c0-52913dfdfb1e

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
theorem _root_.solution (f : V →ₛₗ[σ] V') (A' B' : Submodule S V') :
    relLength (A'.comap f) (B'.comap f) = relLength (LinearMap.range f ⊓ A') B' := by
  rw [← relLength_map_left, Submodule.map_comap_eq]
end GlobalTheory
