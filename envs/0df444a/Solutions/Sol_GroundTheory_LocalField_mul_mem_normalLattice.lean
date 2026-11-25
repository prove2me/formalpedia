-- Prove2me | solution 1 for GroundTheory.LocalField.mul_mem_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:24.076863+00:00
-- url     : https://prove2.me/submissions/96c1f537-5d8c-4cde-8545-12134930d339

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_pow_smul_mem_normalLattice

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
theorem _root_.solution {r : ℕ}
    (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {a b : ℕ} {x y : L}
    (hx : x ∈ normalLattice π θ (a + r)) (hy : y ∈ normalLattice π θ b) :
    x * y ∈ normalLattice π θ (a + b) := by
  obtain ⟨c, rfl⟩ := (mem_normalLattice_iff π θ).mp hx
  obtain ⟨d, rfl⟩ := (mem_normalLattice_iff π θ).mp hy
  have h0 : π ^ r • ∑ σ, ∑ τ, (c σ * d τ) • (σ θ * τ θ) ∈ normalLattice π θ 0 := by
    rw [smul_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [smul_sum]
    refine Submodule.sum_mem _ fun τ _ => ?_
    rw [smul_comm]
    exact Submodule.smul_mem _ _ (hr σ τ)
  have e : (π ^ (a + r) • ∑ σ, c σ • σ θ) * (π ^ b • ∑ τ, d τ • τ θ) =
      π ^ (a + b) • (π ^ r • ∑ σ, ∑ τ, (c σ * d τ) • (σ θ * τ θ)) := by
    rw [smul_smul, ← pow_add, smul_mul_smul_comm, ← pow_add, Finset.sum_mul_sum,
      add_right_comm]
    simp_rw [smul_mul_smul_comm]
  rw [e]
  simpa using pow_smul_mem_normalLattice π θ (u := a + b) h0
end GroundTheory.LocalField
