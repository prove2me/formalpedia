-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.div_mem_filt_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:54:21.457929+00:00
-- url     : https://prove2.me/submissions/faf61704-99d4-4234-a207-1b70ce711672

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_mul_val_inv
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_mul_mem

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
theorem _root_.solution {j : ℕ} {x y : D.units 0} :
    x / y ∈ D.filt.F j ↔ D.val x - D.val y ∈ D.lat (D.k + j) := by
  rw [mem_filt]
  have e1 : D.val (x / y) - 1 = D.val y⁻¹ * (D.val x - D.val y) := by
    rw [div_eq_mul_inv, val_mul]
    linear_combination D.val_mul_val_inv y
  have e2 : D.val x - D.val y = D.val y * (D.val (x / y) - 1) := by
    rw [div_eq_mul_inv, val_mul]
    linear_combination (-D.val x) * D.val_mul_val_inv y
  constructor
  · intro h
    rw [e2]
    exact D.val_mul_mem y h
  · intro h
    rw [e1]
    exact D.val_mul_mem y⁻¹ h
end GroundTheory.LocalField.NormalLatticeData
