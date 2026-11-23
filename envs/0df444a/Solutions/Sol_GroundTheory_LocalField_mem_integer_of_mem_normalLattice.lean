-- Prove2me | solution 1 for GroundTheory.LocalField.mem_integer_of_mem_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:30.632074+00:00
-- url     : https://prove2.me/submissions/9b6efaac-4807-4f97-9d70-071122dc20ef

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_integer_smul_eq
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_algebraMap_mem_integer_iff


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
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]
variable (π : 𝒪[K]) (θ : L)
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution (hθO : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]) {s : ℕ} {x : L}
    (hx : x ∈ normalLattice π θ s) : x ∈ 𝒪[L] := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  rw [integer_smul_eq]
  refine mul_mem ((algebraMap_mem_integer_iff K L _).mpr (π ^ s).2) (sum_mem fun σ _ => ?_)
  rw [integer_smul_eq]
  exact mul_mem ((algebraMap_mem_integer_iff K L _).mpr (c σ).2) (hθO σ)
end GroundTheory.LocalField
