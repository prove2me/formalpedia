-- Prove2me | solution 1 for GoldsteinProj.Conv.supporting_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:03:25.581772+00:00
-- url     : https://prove2.me/submissions/acab18cf-c996-4ef5-a6f4-a3a984a20216

import Mathlib
import Definitions.Def_GoldsteinProj_Conv_Setting

open Filter Topology RealInnerProductSpace

set_option autoImplicit false

open Filter Topology RealInnerProductSpace GoldsteinProj.Conv in
theorem goldstein_318dc9b6_vi {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P) (y : H) :
    ∀ z ∈ C, ⟪y - P y, z - P y⟫ ≤ 0 := by
  obtain ⟨hmem, hmin⟩ := hP y
  have heq : ‖y - P y‖ = ⨅ w : C, ‖y - (w : H)‖ := by
    apply le_antisymm
    · have : Nonempty C := ⟨⟨P y, hmem⟩⟩
      exact le_ciInf (fun w => hmin w w.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩ (⟨P y, hmem⟩ : C)
  exact (norm_eq_iInf_iff_real_inner_le_zero hCv hmem).1 heq

open Filter Topology RealInnerProductSpace GoldsteinProj.Conv in
theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hCv : Convex ℝ C) (P : H → H) (hP : IsProjection C P)
    (f : H → ℝ) (x0 : H) (σ ρ0 : ℝ) (ρ : ℕ → ℝ) (x : ℕ → H)
    (hrun : IsGoldsteinRun f P x0 σ ρ0 ρ x) :
    ∀ k, ∀ z ∈ C,
      ⟪x k - x (k + 1), z⟫ + ⟪x (k + 1), x (k + 1) - x k⟫ ≤ ⟪ρ k • gradient f (x k), z - x (k + 1)⟫ := by
  intro k z hz
  have hx := hrun.2.2 k
  have hvi := goldstein_318dc9b6_vi C hCv P hP (x k - ρ k • gradient f (x k)) z hz
  rw [← hx] at hvi
  have e1 : ⟪x k - x (k + 1), z⟫ + ⟪x (k + 1), x (k + 1) - x k⟫
      = ⟪x k - x (k + 1), z - x (k + 1)⟫ := by
    have hc := real_inner_comm (x k) (x (k + 1))
    simp only [inner_sub_left, inner_sub_right]
    linarith
  have e2 : ⟪x k - ρ k • gradient f (x k) - x (k + 1), z - x (k + 1)⟫
      = ⟪x k - x (k + 1), z - x (k + 1)⟫ - ⟪ρ k • gradient f (x k), z - x (k + 1)⟫ := by
    rw [sub_right_comm, inner_sub_left]
  rw [e1]
  linarith
