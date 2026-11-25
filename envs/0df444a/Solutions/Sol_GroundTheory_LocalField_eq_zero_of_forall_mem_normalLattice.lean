-- Prove2me | solution 1 for GroundTheory.LocalField.eq_zero_of_forall_mem_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:32:35.959305+00:00
-- url     : https://prove2.me/submissions/d06cab3d-0a89-4e94-bdf6-0296cd518cd0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_smul_sum_mem_normalLattice_add_iff
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_forall_pow_dvd

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
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (π : 𝒪[K]) (θ : L)
namespace GroundTheory.LocalField
theorem _root_.solution (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) {s : ℕ} {x : L}
    (h : ∀ N, x ∈ normalLattice π θ (s + N)) : x = 0 := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp (h 0)
  have hc : ∀ σ, c σ = 0 := fun σ => eq_zero_of_forall_pow_dvd hπ fun N =>
    (smul_sum_mem_normalLattice_add_iff π θ hπ.ne_zero hθ s N c).mp (h N) σ
  simp [hc]
end GroundTheory.LocalField
