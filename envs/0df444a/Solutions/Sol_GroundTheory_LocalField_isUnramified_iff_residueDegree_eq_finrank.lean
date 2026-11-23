-- Prove2me | solution 1 for GroundTheory.LocalField.isUnramified_iff_residueDegree_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:37.338968+00:00
-- url     : https://prove2.me/submissions/a39cf5d4-1f19-4ec5-9953-ba5eff4a1c4a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Theorems.Thm_GroundTheory_LocalField_isUnramified_iff
import Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
import Theorems.Thm_GroundTheory_LocalField_residueDegree_pos


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
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
namespace GroundTheory.LocalField
theorem _root_.solution :
    IsUnramified K L ↔ residueDegree K L = Module.finrank K L := by
  rw [isUnramified_iff, ← ramificationIndex_mul_residueDegree K L]
  have h := residueDegree_pos K L
  constructor
  · intro h1
    rw [h1, one_mul]
  · intro h1
    have : ramificationIndex K L * residueDegree K L = 1 * residueDegree K L := by
      rw [one_mul]
      exact h1.symm
    exact Nat.eq_of_mul_eq_mul_right h this
end GroundTheory.LocalField
