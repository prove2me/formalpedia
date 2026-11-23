-- Prove2me | solution 1 for GroundTheory.LocalField.exists_normalizedValuation_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:13:12.212288+00:00
-- url     : https://prove2.me/submissions/525a6e69-d2e6-47fa-a7d5-fe0265d9ca07

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (K)
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℤ) :
    ∃ y : K, normalizedValuation K y = WithZero.exp n := by
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).symm (WithZero.exp n))
  exact ⟨y, by rw [normalizedValuation_apply, hy]; simp⟩
end GroundTheory.LocalField
