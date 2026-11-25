-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.val_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:04.922852+00:00
-- url     : https://prove2.me/submissions/11d40076-bfa3-4ddc-aa1c-522b55947f98

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_sub_one_mem

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
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
open GroundTheory.LocalField.NormalLatticeData
variable (D : NormalLatticeData K L)
attribute [local instance] action
namespace GroundTheory.LocalField.NormalLatticeData
theorem _root_.solution (x : D.units 0) {t : ℕ} {z : L} (hz : z ∈ D.lat t) : D.val x * z ∈ D.lat t := by
  have e : D.val x * z = z + (D.val x - 1) * z := by ring
  rw [e]
  exact add_mem hz (D.lat_antitone (Nat.le_succ t) (D.mul_mem_lat le_rfl (D.val_sub_one_mem x) hz))
end GroundTheory.LocalField.NormalLatticeData
