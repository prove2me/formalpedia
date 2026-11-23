-- Prove2me | solution 1 for GroundTheory.LocalField.coeff_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:59.495436+00:00
-- url     : https://prove2.me/submissions/13c88995-921d-4151-85f5-1c4f1d9514c8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice

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
theorem _root_.solution (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    {c d : Gal(L/K) → 𝒪[K]} (h : ∑ σ, c σ • σ θ = ∑ σ, d σ • σ θ) : c = d := by
  have h0 : ∑ σ, ((c σ : K) - d σ) • σ θ = 0 := by
    simp_rw [sub_smul, sum_sub_distrib]
    exact sub_eq_zero.mpr h
  funext σ
  exact Subtype.ext (sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hθ _ h0 σ))
end GroundTheory.LocalField
