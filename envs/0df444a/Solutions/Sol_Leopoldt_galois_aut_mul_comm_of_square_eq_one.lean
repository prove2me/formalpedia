-- Prove2me | solution 1 for Leopoldt.galois_aut_mul_comm_of_square_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T22:24:42.26461+00:00
-- url     : https://prove2.me/submissions/4de4a2ed-f046-43c2-a7d2-8cc3677555dd

import Definitions.Def_LeopoldtDefect
import Mathlib.Tactic.Group

open NumberField

theorem solution
    (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (h : ∀ σ : K ≃ₐ[ℚ] K, σ * σ = 1)
    (σ τ : K ≃ₐ[ℚ] K) : σ * τ = τ * σ := by
  have hσ : σ⁻¹ = σ := by
    calc
      σ⁻¹ = σ⁻¹ * (σ * σ) := by rw [h σ, mul_one]
      _ = σ := by group
  have hτ : τ⁻¹ = τ := by
    calc
      τ⁻¹ = τ⁻¹ * (τ * τ) := by rw [h τ, mul_one]
      _ = τ := by group
  have hστ : (σ * τ)⁻¹ = σ * τ := by
    calc
      (σ * τ)⁻¹ = (σ * τ)⁻¹ * ((σ * τ) * (σ * τ)) := by rw [h (σ * τ), mul_one]
      _ = σ * τ := by group
  calc
    σ * τ = (σ * τ)⁻¹ := hστ.symm
    _ = τ⁻¹ * σ⁻¹ := mul_inv_rev σ τ
    _ = τ * σ := by rw [hτ, hσ]
