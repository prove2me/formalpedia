-- Prove2me | solution 1 for GroundTheory.LocalField.unitsOrd_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:34:05.070266+00:00
-- url     : https://prove2.me/submissions/43bc73f9-c284-4ff0-8b64-3104176e837f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
import Theorems.Thm_GroundTheory_LocalField_unitsOrd_ofMul
import Theorems.Thm_GroundTheory_LocalField_ord_uniformizer


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
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
namespace GroundTheory.LocalField
theorem _root_.solution : Function.Surjective (unitsOrd L) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  intro n
  refine ⟨n • Additive.ofMul (uniformizerUnit hϖ), ?_⟩
  rw [map_zsmul, unitsOrd_ofMul, coe_uniformizerUnit, ord_uniformizer hϖ, smul_eq_mul, mul_one]
end GroundTheory.LocalField
