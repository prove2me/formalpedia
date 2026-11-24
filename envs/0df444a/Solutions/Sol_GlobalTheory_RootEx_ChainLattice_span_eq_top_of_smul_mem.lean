-- Prove2me | solution 1 for GlobalTheory.RootEx.ChainLattice.span_eq_top_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T13:37:40.896301+00:00
-- url     : https://prove2.me/submissions/37604806-cad1-44c2-bbc2-a3df34734049

import Mathlib

open Submodule

theorem solution {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]
    (M : Submodule R V) (h : ∀ v : V, ∃ a : R, a ≠ 0 ∧ a • v ∈ M) :
    Submodule.span K (M : Set V) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  obtain ⟨a, ha0, hav⟩ := h v
  have haK : algebraMap R K a ≠ 0 := by
    intro hz
    apply ha0
    exact IsFractionRing.injective R K (by rw [map_zero]; exact hz)
  have hmem : algebraMap R K a • v ∈ Submodule.span K (M : Set V) := by
    rw [algebraMap_smul]
    exact Submodule.subset_span hav
  have hv : v = (algebraMap R K a)⁻¹ • (algebraMap R K a • v) := by
    rw [smul_smul, inv_mul_cancel₀ haK, one_smul]
  rw [hv]
  exact Submodule.smul_mem _ _ hmem