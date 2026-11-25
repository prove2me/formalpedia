-- Prove2me | solution 1 for GroundTheory.LocalField.ord_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:49:38.891064+00:00
-- url     : https://prove2.me/submissions/bf86bdfd-c991-4a38-b0e7-7479195561b4

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_valuation_algEquiv_apply


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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution (σ : L ≃ₐ[K] L) (x : L) : ord (σ x) = ord x := by
  rw [ord, ord, normalizedValuation_apply, normalizedValuation_apply,
    valuation_algEquiv_apply K L σ x]
end GroundTheory.LocalField
