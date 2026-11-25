-- Prove2me | solution 1 for GroundTheory.LocalField.smul_sum_mem_normalLattice_add_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:23:25.790064+00:00
-- url     : https://prove2.me/submissions/23303246-0aae-4bea-9ed3-af3ca51064cc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_integer_smul_cancel
import Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
import Theorems.Thm_GroundTheory_LocalField_coeff_injective

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
theorem _root_.solution (hπ : π ≠ 0)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (s N : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ ∈ normalLattice π θ (s + N) ↔ ∀ σ, π ^ N ∣ c σ := by
  constructor
  · intro h
    obtain ⟨d, hd⟩ := (mem_normalLattice_iff π θ).mp h
    have e : π ^ s • ∑ σ, (π ^ N * d σ) • σ θ = π ^ s • ∑ σ, c σ • σ θ := by
      rw [← hd, pow_add, mul_smul]
      simp_rw [smul_sum, mul_smul]
    have := coeff_injective θ hθ (integer_smul_cancel (pow_ne_zero s hπ) e)
    intro σ
    exact ⟨d σ, (congrFun this σ).symm⟩
  · intro h
    choose d hd using h
    refine (mem_normalLattice_iff π θ).mpr ⟨d, ?_⟩
    rw [pow_add, mul_smul]
    simp_rw [smul_sum, ← mul_smul, hd]
end GroundTheory.LocalField
