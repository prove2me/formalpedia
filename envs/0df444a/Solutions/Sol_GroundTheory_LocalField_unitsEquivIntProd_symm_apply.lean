-- Prove2me | solution 1 for GroundTheory.LocalField.unitsEquivIntProd_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:11:47.681825+00:00
-- url     : https://prove2.me/submissions/70c532b1-9940-47f6-bdfb-0e4d0b9ece1a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic

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
open ValuativeRel IsLocalRing
open scoped WithZero
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {K}
namespace GroundTheory.LocalField
theorem _root_.solution {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ)
    (p : Multiplicative ℤ × 𝒪[K]ˣ) :
    (unitsEquivIntProd hϖ).symm p = unitsOfIntProd hϖ p := rfl
end GroundTheory.LocalField
