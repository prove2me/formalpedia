-- Prove2me | solution 1 for GlobalTheory.LengthCommensurable.signedLength_map_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:04:54.747581+00:00
-- url     : https://prove2.me/submissions/2a820d27-e3a3-42de-9457-23379a93b167

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_LengthCommensurable_signedLength_map_of_injective

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
namespace LengthCommensurable
theorem _root_.solution {A B : Submodule R V}
    (h : LengthCommensurable A B) (e : V ≃ₛₗ[σ] V') :
    signedLength (A.map (e : V →ₛₗ[σ] V')) (B.map (e : V →ₛₗ[σ] V')) = signedLength A B :=
  h.signedLength_map_of_injective _ e.injective
end LengthCommensurable
end GlobalTheory
