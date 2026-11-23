-- Prove2me | solution 1 for GroundTheory.LocalField.pow_smul_mem_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:30.667995+00:00
-- url     : https://prove2.me/submissions/0d0ece94-d6d1-4e04-a7ff-3ce2ab2e688f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_smul_sum_mem_normalLattice

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
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable (π : 𝒪[K]) (θ : L)
namespace GroundTheory.LocalField
theorem _root_.solution {t u : ℕ} {x : L} (hx : x ∈ normalLattice π θ t) :
    π ^ u • x ∈ normalLattice π θ (t + u) := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [← mul_smul, ← pow_add, add_comm u t]
  exact smul_sum_mem_normalLattice π θ _ c
end GroundTheory.LocalField
