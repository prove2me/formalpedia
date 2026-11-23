-- Prove2me | solution 1 for GroundTheory.LocalField.teichmuller_pow_card_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:02:58.45492+00:00
-- url     : https://prove2.me/submissions/88ca6fd6-3d2e-4c1f-bfbc-f8481b2c0212

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsRootOfAdicComplete
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Polynomial
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
variable (K)
variable {K}
variable (K)
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution (ζ : 𝓀[K]ˣ) :
    teichmuller K ζ ^ (Nat.card 𝓀[K] - 1) = 1 :=
  (exists_teichmuller_lift ζ).choose_spec.1
end GroundTheory.LocalField
