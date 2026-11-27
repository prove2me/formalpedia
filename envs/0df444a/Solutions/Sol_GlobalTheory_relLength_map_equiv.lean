-- Prove2me | solution 1 for GlobalTheory.relLength_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:42:08.568238+00:00
-- url     : https://prove2.me/submissions/02d5cb76-691b-4f51-9398-4d679d92d98a

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
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} {σ' : S →+* R}
  [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [RingHomSurjective σ]
namespace GlobalTheory
theorem _root_.solution (e : V ≃ₛₗ[σ] V') (A B : Submodule R V) :
    relLength (A.map (e : V →ₛₗ[σ] V')) (B.map (e : V →ₛₗ[σ] V')) = relLength A B :=
  relLength_map_of_injective _ e.injective A B
end GlobalTheory
