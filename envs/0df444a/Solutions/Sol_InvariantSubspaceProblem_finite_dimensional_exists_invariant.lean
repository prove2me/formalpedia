-- Prove2me | solution 1 for InvariantSubspaceProblem.finite_dimensional_exists_invariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T16:05:48.563727+00:00
-- url     : https://prove2.me/submissions/3bcecc02-e454-4553-af93-bf00c131be75

import Mathlib
import Definitions.Def_InvariantSubspaceProblem_Defs

open InvariantSubspaceProblem in
theorem solution (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (hdim : 2 ≤ Module.finrank ℂ E)
    (T : E →L[ℂ] E) : HasNontrivialClosedInvariantSubspace T := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := ℂ) (by omega)
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (T : E →ₗ[ℂ] E)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  refine ⟨Submodule.span ℂ {v}, Submodule.closed_of_finiteDimensional _, ?_, ?_, ?_⟩
  · rw [Ne, Submodule.span_singleton_eq_bot]; exact hv.2
  · intro h
    have h1 := finrank_span_singleton (K := ℂ) hv.2
    rw [h, finrank_top] at h1
    omega
  · intro x hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hx
    rw [map_smul]
    have : T v = μ • v := hv.apply_eq_smul
    rw [this, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
