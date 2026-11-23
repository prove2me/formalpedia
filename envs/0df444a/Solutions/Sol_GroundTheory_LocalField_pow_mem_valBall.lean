-- Prove2me | solution 1 for GroundTheory.LocalField.pow_mem_valBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:52.588836+00:00
-- url     : https://prove2.me/submissions/134dea4a-1244-4f21-bb1b-f3428c851bf0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_mem_valBall
import Theorems.Thm_GroundTheory_LocalField_mul_mem_valBall
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
theorem _root_.solution {n : ℤ} {x : K} (hx : x ∈ valBall K n) (k : ℕ) :
    x ^ k ∈ valBall K (k * n) := by
  induction k with
  | zero => simp [mem_valBall]
  | succ k ih =>
    rw [pow_succ]
    convert mul_mem_valBall ih hx using 2
    push_cast; ring
end GroundTheory.LocalField
