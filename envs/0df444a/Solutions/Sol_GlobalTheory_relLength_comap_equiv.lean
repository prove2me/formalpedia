-- Prove2me | solution 1 for GlobalTheory.relLength_comap_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:40:41.583466+00:00
-- url     : https://prove2.me/submissions/35c7708f-d5fb-4d13-a25f-ff3fca5e80f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_relLength_comap_of_surjective

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
theorem _root_.solution (e : V ≃ₛₗ[σ] V') (A' B' : Submodule S V') :
    relLength (A'.comap (e : V →ₛₗ[σ] V')) (B'.comap (e : V →ₛₗ[σ] V')) = relLength A' B' :=
  relLength_comap_of_surjective _ e.surjective A' B'
end GlobalTheory
