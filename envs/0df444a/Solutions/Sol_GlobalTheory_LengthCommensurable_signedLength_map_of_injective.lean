-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_map_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:29:29.065364+00:00
-- url     : https://prove2.me/submissions/21768c53-5d89-4a7d-9e97-30f8909e7ce5

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
namespace LengthCommensurable
theorem _root_.solution {A B : Submodule R V}
    (_h : LengthCommensurable A B) (f : V →ₛₗ[σ] V') (hf : Function.Injective f) :
    signedLength (A.map f) (B.map f) = signedLength A B := by
  simp only [signedLength, relLength_map_of_injective f hf]
end LengthCommensurable
end GlobalTheory
