-- Prove2me | solution 1 for GroundTheory.LocalField.algEquiv_mem_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:55.27219+00:00
-- url     : https://prove2.me/submissions/7a41c8b3-f6db-4602-90e6-8d9c96284904

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_smul_sum_mem_normalLattice
import Theorems.Thm_GroundTheory_LocalField_algEquiv_smul_sum

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
theorem _root_.solution (τ : Gal(L/K)) {s : ℕ} {x : L} (hx : x ∈ normalLattice π θ s) :
    τ x ∈ normalLattice π θ s := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [algEquiv_smul_sum]
  exact smul_sum_mem_normalLattice π θ s _
end GroundTheory.LocalField
