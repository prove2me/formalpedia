-- Prove2me | solution 1 for HolisticService.Effort.optimal_price
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T09:48:12.55438+00:00
-- url     : https://prove2.me/submissions/cb2c8082-5480-484f-9241-1dd0c5c9a5d8

import Mathlib
import Definitions.Def_HolisticService_Effort_Model

open HolisticService.Effort

theorem solution {n : ℕ} (M : Params n) (δ : Fin n → ℝ) (hδ : ∀ i, 0 ≤ δ i ∧ δ i ≤ 1) (π : ℝ) :
    IsOptimalDesign M δ π ↔
      π = πtil M δ ∧ ∀ δ' : Fin n → ℝ, (∀ i, 0 ≤ δ' i ∧ δ' i ≤ 1) → Utilde M δ' ≤ Utilde M δ := by
  -- `𝒰` is `(terms in δ) − π`, and feasibility is `π ≥ π̃(δ)`.
  have hu : ∀ δ π, utility M δ π = Utilde M δ + (πtil M δ - π) := by
    intro δ π; unfold Utilde utility; ring
  have hfeas : ∀ δ π, Feasible M δ π ↔ (∀ i, 0 ≤ δ i ∧ δ i ≤ 1) ∧ πtil M δ ≤ π := by
    intro δ π; unfold Feasible πtil; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
  constructor
  · rintro ⟨hF, hmax⟩
    have hF' := (hfeas δ π).1 hF
    have h1 := hmax δ (πtil M δ) ((hfeas _ _).2 ⟨hδ, le_rfl⟩)
    rw [hu, hu] at h1
    have hπ : π = πtil M δ := by linarith [hF'.2]
    refine ⟨hπ, fun δ' hδ' => ?_⟩
    have h2 := hmax δ' (πtil M δ') ((hfeas _ _).2 ⟨hδ', le_rfl⟩)
    rw [hu, hu, hπ] at h2
    linarith
  · rintro ⟨hπ, hmax⟩
    refine ⟨(hfeas _ _).2 ⟨hδ, hπ.ge⟩, fun δ' π' hF => ?_⟩
    have hF' := (hfeas δ' π').1 hF
    rw [hu, hu, hπ]
    have := hmax δ' hF'.1
    linarith [hF'.2]
