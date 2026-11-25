-- Prove2me | solution 1 for GroundTheory.LocalField.NormalLatticeData.grHom_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:21:49.685271+00:00
-- url     : https://prove2.me/submissions/2f8b2fda-d7a9-468c-b161-1206fd09668e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_grHom_toAdd

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
theorem _root_.solution {j : ℕ} (x : D.filt.F j) :
    D.grHom j x = 1 ↔ (x : D.units 0) ∈ D.filt.F (j + 1) := by
  rw [← toAdd_eq_zero, grHom_toAdd, QuotientAddGroup.eq_zero_iff, Submodule.mem_toAddSubgroup,
    mem_filt]
  rfl
end GroundTheory.LocalField.NormalLatticeData
