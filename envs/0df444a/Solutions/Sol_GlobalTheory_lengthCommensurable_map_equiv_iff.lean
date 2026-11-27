-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_map_equiv_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:02.308783+00:00
-- url     : https://prove2.me/submissions/e4c91b62-9476-4b74-bbd6-2c2337d42d17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_lengthCommensurable_map_iff_of_injective

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
theorem _root_.solution (e : V ≃ₛₗ[σ] V') {A B : Submodule R V} :
    LengthCommensurable (A.map (e : V →ₛₗ[σ] V')) (B.map (e : V →ₛₗ[σ] V')) ↔
      LengthCommensurable A B :=
  lengthCommensurable_map_iff_of_injective _ e.injective
end GlobalTheory
