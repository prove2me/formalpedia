-- Prove2me | solution 1 for GlobalTheory.TopExt.dualEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:35:21.314248+00:00
-- url     : https://prove2.me/submissions/0c626d35-fb4a-4083-9bc7-7dc663a6fb60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemHomogIffIsHomogeneous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsDetEquivOfSubsingleton

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module Function
open GlobalTheory
open GlobalTheory.TopExt
variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]
namespace GlobalTheory.TopExt
theorem _root_.solution [Module.Finite R F] [Module.Projective R F] (n : ℕ)
    (ξ : ⋀[R]^n (Dual R F)) : dualEquiv R F n ξ = exteriorPower.pairingDual R F n ξ := rfl
end GlobalTheory.TopExt
