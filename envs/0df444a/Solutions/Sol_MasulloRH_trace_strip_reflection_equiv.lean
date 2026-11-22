-- Prove2me | solution 1 for MasulloRH.trace_strip_reflection_equiv
-- status  : ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-22T01:56:06.209358+00:00
-- url     : https://prove2.me/submissions/45af20e9-6d45-46b7-91ec-23c2d835a8be

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false
open MeasureTheory Set
open scoped Topology ContDiff
open MasulloRH

theorem solution (α : ℝ)
    (hFE : ∀ z : ℂ, riemannZeta z = 0 ↔ riemannZeta (1 - z) = 0) :
    ∃ e : ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip α,
      ∀ ρ, (e ρ).val = 1 - ρ.val := by
  let f : ZetaZerosInTraceStrip α → ZetaZerosInTraceStrip α := fun ρ =>
    ⟨1 - (ρ : ℂ), by
      have hz : riemannZeta (1 - (ρ : ℂ)) = 0 := (hFE (ρ : ℂ)).mp ρ.property.1
      have hre : (1 - (ρ : ℂ)).re = 1 - ρ.val.re := by simp
      have hpos : 0 < (1 - (ρ : ℂ)).re := by
        rw [hre]
        linarith [ρ.property.2.2.1]
      have hlt : (1 - (ρ : ℂ)).re < 1 := by
        rw [hre]
        linarith [ρ.property.2.1]
      have habs : |(1 - (ρ : ℂ)).re - 1 / 2| = |ρ.val.re - 1 / 2| := by
        rw [hre]
        rw [show (1 - ρ.val.re - 1 / 2 : ℝ) = -(ρ.val.re - 1 / 2) by ring]
        rw [abs_neg]
      exact ⟨hz, hpos, hlt, by rw [habs]; exact ρ.property.2.2.2⟩⟩
  let e : ZetaZerosInTraceStrip α ≃ ZetaZerosInTraceStrip α :=
    { toFun := f
      invFun := f
      left_inv := by
        intro ρ
        apply Subtype.ext
        dsimp [f]
        apply Complex.ext <;> norm_num
      right_inv := by
        intro ρ
        apply Subtype.ext
        dsimp [f]
        apply Complex.ext <;> norm_num }
  refine ⟨e, ?_⟩
  intro ρ
  rfl
