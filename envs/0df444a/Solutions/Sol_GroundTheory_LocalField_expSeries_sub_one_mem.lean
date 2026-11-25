-- Prove2me | solution 1 for GroundTheory.LocalField.expSeries_sub_one_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:45:19.278814+00:00
-- url     : https://prove2.me/submissions/b8a88742-9371-48d7-84c8-959543883e0e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExamplesCharZero
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
import Theorems.Thm_GroundTheory_LocalField_expSeries_sub_one_sub_self_mem
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
variable (p : ℕ) [hp : Fact p.Prime] [CharP 𝓀[K] p] [CharZero K]
namespace GroundTheory.LocalField
theorem _root_.solution {a : ℤ} {x : K} (hx : x ∈ valBall K a)
    (ha : (absRamificationIndex K : ℤ) < (p - 1 : ℤ) * a) :
    expSeries x - 1 ∈ valBall K a := by
  have h := add_mem (valBall_antitone (by omega : a ≤ a + 1)
    (expSeries_sub_one_sub_self_mem p hx ha)) hx
  simpa using h
end GroundTheory.LocalField
