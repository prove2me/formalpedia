-- Prove2me | solution 1 for GroundTheory.LocalField.algEquiv_smul_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:27.37257+00:00
-- url     : https://prove2.me/submissions/719b5df4-1dc6-4d68-b6ee-02d37ddc5e69

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_integer_smul_eq

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
theorem _root_.solution (τ : Gal(L/K)) (s : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    τ (π ^ s • ∑ σ, c σ • σ θ) = π ^ s • ∑ σ, c (τ⁻¹ * σ) • σ θ := by
  have h : ∀ (a : 𝒪[K]) (y : L), τ (a • y) = a • τ y := fun a y => by
    rw [integer_smul_eq, integer_smul_eq, map_mul, AlgEquiv.commutes]
  rw [h, map_sum]
  congr 1
  simp_rw [h, ← AlgEquiv.mul_apply]
  exact Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun σ => by simp)
end GroundTheory.LocalField
