-- Prove2me | solution 1 for MatousekLP.Duality.primitive_cone_closed
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T04:02:45.089472+00:00
-- url     : https://prove2.me/submissions/4699367b-8c81-4cb0-8c01-afb6a4447ed9

import Definitions.Def_MatousekLP_Duality_Cones
import Mathlib

open MatousekLP.Duality

theorem solution {m : ℕ} (P : Set (EuclideanSpace ℝ (Fin m)))
    (hP : IsPrimitiveCone P) : IsClosed P := by
  obtain ⟨k, -, v, hv, rfl⟩ := hP
  -- the cone is the image of the nonnegative orthant under t ↦ ∑ tᵢ vᵢ
  set L : (Fin k → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := Fintype.linearCombination ℝ v
  have hL : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hv.fintypeLinearCombination_injective
  have hemb := LinearMap.isClosedEmbedding_of_injective hL
  have himage : coneGen v = L '' {t | ∀ i, 0 ≤ t i} := by
    ext x
    simp only [coneGen, Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simp [L, Fintype.linearCombination_apply]⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t, ht, by simp [L, Fintype.linearCombination_apply]⟩
  rw [himage]
  apply hemb.isClosedMap
  have : {t : Fin k → ℝ | ∀ i, 0 ≤ t i} = ⋂ i, {t | 0 ≤ t i} := by ext; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
