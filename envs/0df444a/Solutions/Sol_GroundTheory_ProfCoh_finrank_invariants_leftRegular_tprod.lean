-- Prove2me | solution 1 for GroundTheory.ProfCoh.finrank_invariants_leftRegular_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:49:31.371919+00:00
-- url     : https://prove2.me/submissions/68c36ca8-0413-4253-97b9-3e98419e2bfe

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_CoprimeRegular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open Representation TensorProduct
variable {k Γ N : Type*} [CommRing k] [Group Γ] [Fintype Γ] [DecidableEq Γ] [AddCommGroup N]
  [Module k N] (σ : Representation k Γ N)
namespace GroundTheory.ProfCoh
theorem _root_.solution :
    Module.finrank k ((leftRegular k Γ).tprod σ).invariants = Module.finrank k N :=
  (invariantsLeftRegularTensorEquiv σ).finrank_eq
end GroundTheory.ProfCoh
