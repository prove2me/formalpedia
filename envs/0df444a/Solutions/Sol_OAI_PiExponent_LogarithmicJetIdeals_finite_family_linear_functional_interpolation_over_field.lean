-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.finite_family_linear_functional_interpolation_over_field
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T07:49:35.660984+00:00
-- url     : https://prove2.me/submissions/29fb92bb-e1a8-45e3-8e3f-67936248c5a9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_exists_biorthogonal_vectors

theorem solution
    {K ι V : Type} [Field K] [Fintype ι] [AddCommMonoid V] [Module K V]
    (L : ι → V →ₗ[K] K)
    (hL : LinearIndependent K L)
    (values : ι → K) :
    ∃ v : V, ∀ i, L i v = values i := by
  classical
  obtain ⟨w, hw⟩ :=
    OAI.PiExponent.LogarithmicJetIdeals.exists_biorthogonal_vectors L hL
  refine ⟨∑ j, values j • w j, ?_⟩
  intro i
  rw [map_sum]
  simp only [map_smul]
  simp [hw]