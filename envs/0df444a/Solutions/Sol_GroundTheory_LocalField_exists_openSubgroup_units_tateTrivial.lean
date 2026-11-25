-- Prove2me | solution 1 for GroundTheory.LocalField.exists_openSubgroup_units_tateTrivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:25:32.80552+00:00
-- url     : https://prove2.me/submissions/a64dc837-c126-435c-8b5c-9d6c0049428d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_nonempty
import Theorems.Thm_GroundTheory_LocalField_normalLattice_eq_smul_span
import Theorems.Thm_GroundTheory_LocalField_span_conjugates_eq_top
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_isOpen_units
import Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_subsingleton_tate

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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
open scoped Pointwise
namespace GroundTheory.LocalField
theorem _root_.solution :
    ∃ (π : 𝒪[K]) (θ : L) (k : ℕ), Irreducible π ∧ (LinearIndependent K fun σ : Gal(L/K) => σ θ) ∧
      Submodule.span K (Set.range fun σ : Gal(L/K) => σ θ) = ⊤ ∧
      (∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]) ∧
      ∃ (V : Subgroup 𝒪[L]ˣ)
        (hV : ∀ σ : Gal(L/K), ∀ u ∈ V, ∃ w ∈ V, ((w : 𝒪[L]) : L) = σ ((u : 𝒪[L]) : L)),
        (∀ u : 𝒪[L]ˣ, u ∈ V ↔
          ((u : 𝒪[L]) : L) - 1 ∈ π ^ k • Submodule.span 𝒪[K] (Set.range fun σ : Gal(L/K) => σ θ)) ∧
        IsOpen (V : Set 𝒪[L]ˣ) ∧
        (letI := stableUnitsAction V hV;
          Subsingleton (TateZero Gal(L/K) V) ∧ Subsingleton (TateNegOne Gal(L/K) V)) := by
  obtain ⟨D⟩ := NormalLatticeData.nonempty K L
  refine ⟨D.π, D.θ, D.k, D.irreducible, D.linearIndependent,
    span_conjugates_eq_top D.linearIndependent, D.integer, D.units 0, D.units_zero_stable,
    fun u => ?_, D.isOpen_units 0, D.subsingleton_tate⟩
  rw [← normalLattice_eq_smul_span]
  exact Iff.rfl
end GroundTheory.LocalField
