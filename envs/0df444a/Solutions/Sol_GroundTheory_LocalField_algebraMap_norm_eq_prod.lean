-- Prove2me | solution 1 for GroundTheory.LocalField.algebraMap_norm_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:45:23.979193+00:00
-- url     : https://prove2.me/submissions/2bc2269a-47f5-4a94-9d01-8142b0656181

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors
variable (K L : Type*) [Field K] [Field L] [Algebra K L]
namespace GroundTheory.LocalField
theorem _root_.solution [FiniteDimensional K L] [IsGalois K L] (x : L) :
    algebraMap K L (Algebra.norm K x) = ∏ σ : L ≃ₐ[K] L, σ x :=
  Algebra.norm_eq_prod_automorphisms K x
end GroundTheory.LocalField
