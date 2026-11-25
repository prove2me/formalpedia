-- Prove2me | solution 1 for GroundTheory.LocalField.exists_normalBasis_integer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:25:40.894309+00:00
-- url     : https://prove2.me/submissions/9588c5e0-390b-4897-929a-44f09b7deee8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_exists_pow_mul_mem_integer_of_lt_one
import Theorems.Thm_GroundTheory_LocalField_valuation_algebraMap_lt_one

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
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]
variable [IsGalois K L]
namespace GroundTheory.LocalField
theorem _root_.solution {π : 𝒪[K]} (hπ : Irreducible π) :
    ∃ θ : L, (LinearIndependent K fun σ : Gal(L/K) => σ θ) ∧ ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L] := by
  let θ₀ : L := IsGalois.normalBasis K L 1
  have hθ₀ : LinearIndependent K fun σ : Gal(L/K) => σ θ₀ := by
    have := (IsGalois.normalBasis K L).linearIndependent
    convert this using 1
    funext σ
    rw [IsGalois.normalBasis_apply]
  choose n hn using fun σ : Gal(L/K) =>
    exists_pow_mul_mem_integer_of_lt_one (valuation_algebraMap_lt_one (L := L) hπ) (σ θ₀)
  let c : K := (π : K) ^ univ.sup n
  have hc : c ≠ 0 := pow_ne_zero _ fun h => hπ.ne_zero (Subtype.ext h)
  refine ⟨c • θ₀, ?_, fun σ => ?_⟩
  · rw [Fintype.linearIndependent_iff] at hθ₀ ⊢
    intro g hg σ
    have := hθ₀ (fun τ => g τ * c) (by simpa [map_smul, smul_smul] using hg) σ
    exact (mul_eq_zero.mp this).resolve_right hc
  · rw [map_smul, Algebra.smul_def, map_pow]
    exact hn σ _ (le_sup (mem_univ σ))
end GroundTheory.LocalField
