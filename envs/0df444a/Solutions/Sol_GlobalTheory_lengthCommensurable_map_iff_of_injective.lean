-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_map_iff_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:24.719798+00:00
-- url     : https://prove2.me/submissions/e7e703d2-452e-4c6d-9e7a-fe3cb5d75f56

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
theorem _root_.solution (f : V →ₛₗ[σ] V') (hf : Function.Injective f)
    {A B : Submodule R V} :
    LengthCommensurable (A.map f) (B.map f) ↔ LengthCommensurable A B := by
  simp only [LengthCommensurable, relLength_map_of_injective f hf]
end GlobalTheory
