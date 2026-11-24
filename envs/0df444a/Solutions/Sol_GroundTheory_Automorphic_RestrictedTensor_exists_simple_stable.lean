-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.exists_simple_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:58:55.276649+00:00
-- url     : https://prove2.me/submissions/501b09ab-c993-4b14-85c6-acdc7b77a92a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module
variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable [FiniteDimensional ℂ M]
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution (T : Set (End ℂ M)) [Nontrivial M] :
    ∃ (N : Submodule ℂ M) (hN : IsStable T N), N ≠ ⊥ ∧ IsSimpleUnder (restrictSet T N hN) := by
  classical
  have hex : ∃ d, ∃ N : Submodule ℂ M, N ≠ ⊥ ∧ IsStable T N ∧ Module.finrank ℂ N = d :=
    ⟨_, ⊤, top_ne_bot, fun _ _ _ _ => trivial, rfl⟩
  obtain ⟨N, hN0, hNs, hNd⟩ := Nat.find_spec hex
  have hmin : ∀ N' : Submodule ℂ M, N' ≠ ⊥ → IsStable T N' → Module.finrank ℂ N ≤ Module.finrank ℂ N' :=
    fun N' h1 h2 => hNd ▸ Nat.find_min' hex ⟨N', h1, h2, rfl⟩
  refine ⟨N, hNs, hN0, ?_, ?_⟩
  · exact Submodule.nontrivial_iff_ne_bot.2 hN0
  · intro q hq
    by_cases hq0 : q = ⊥
    · exact Or.inl hq0
    right
    have hst : IsStable T (q.map N.subtype) := by
      rintro t ht _ ⟨x, hx, rfl⟩
      exact ⟨(t : End ℂ M).restrict (hNs t ht) x, hq _ ⟨⟨t, ht⟩, rfl⟩ x hx, rfl⟩
    have hne : q.map N.subtype ≠ ⊥ := by
      intro h0
      apply hq0
      rw [eq_bot_iff]
      intro x hx
      have : (x : M) ∈ q.map N.subtype := ⟨x, hx, rfl⟩
      rw [h0, Submodule.mem_bot] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
    have hle := hmin _ hne hst
    rw [Submodule.finrank_map_subtype_eq] at hle
    exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le q) hle)
end GroundTheory.Automorphic.RestrictedTensor
