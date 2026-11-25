-- Prove2me | solution 1 for GroundTheory.LocalField.natCard_tateZero_units_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:52.572908+00:00
-- url     : https://prove2.me/submissions/43ec635a-55b2-42d9-994e-e3943259020e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_unitsToTateZero_surjective
import Theorems.Thm_GroundTheory_LocalField_ker_unitsToTateZero

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
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Nat.card (Kˣ ⧸ (normUnits K L).range) := by
  rw [← ker_unitsToTateZero]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ unitsToTateZero_surjective).toEquiv.symm
end GroundTheory.LocalField
