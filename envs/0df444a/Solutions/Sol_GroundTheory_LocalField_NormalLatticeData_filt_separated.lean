-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.filt_separated
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:49:03.228444+00:00
-- url     : https://prove2.me/submissions/1effa914-eb60-430e-ab19-a8ba6f769cc1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_injective
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_forall_mem_normalLattice


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
theorem _root_.solution : FiltrationSeparated D.filt.F := by
  intro x hx
  have h0 : D.val x - 1 = 0 := eq_zero_of_forall_mem_normalLattice D.π D.θ D.irreducible
    D.linearIndependent (s := D.k) fun N => hx N
  exact D.val_injective (by rw [val_one]; exact sub_eq_zero.mp h0)
end GroundTheory.LocalField.NormalLatticeData
