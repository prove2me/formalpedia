-- Prove2me | solution 1 for GroundTheory.LocalField.isOpen_valBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:37.767516+00:00
-- url     : https://prove2.me/submissions/22e3dc3c-f35c-475e-bfbe-4d1c759fe5dd

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_exists_normalizedValuation_eq
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_isOpen_setOf_valuation_sub_le
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
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℤ) : IsOpen (valBall K n : Set K) := by
  obtain ⟨y, hy⟩ := exists_normalizedValuation_eq K (-n)
  have hy0 : valuation K y ≠ 0 := by
    intro h
    rw [normalizedValuation_apply, h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have : (valBall K n : Set K) = {z : K | valuation K (z - 0) ≤ valuation K y} := by
    ext z
    simp only [sub_zero, SetLike.mem_coe, mem_valBall, ← hy, normalizedValuation_le_iff]
    rfl
  rw [this]
  exact isOpen_setOf_valuation_sub_le hy0
end GroundTheory.LocalField
