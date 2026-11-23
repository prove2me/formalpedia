-- Prove2me | solution 1 for GroundTheory.LocalField.unitsEquivResidueProd_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:33.821717+00:00
-- url     : https://prove2.me/submissions/6c6d9748-a1de-4798-adea-78bc1ea12f44

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
theorem _root_.solution (u : 𝒪[K]ˣ) :
    (unitsEquivResidueProd K u).1 = unitsToResidue K u := rfl
end GroundTheory.LocalField
