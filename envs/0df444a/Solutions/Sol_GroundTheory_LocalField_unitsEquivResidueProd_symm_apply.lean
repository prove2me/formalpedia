-- Prove2me | solution 1 for GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:33.944045+00:00
-- url     : https://prove2.me/submissions/cc020692-fc52-48e0-9c36-09503acc3203

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
variable (K)
namespace GroundTheory.LocalField
theorem _root_.solution (ζ : 𝓀[K]ˣ) (v : unitFiltration K 1) :
    (unitsEquivResidueProd K).symm (ζ, v) = teichmuller K ζ * v := rfl
end GroundTheory.LocalField
