-- Prove2me | solution 1 for GeomDL.Blueprint.sidenote_p20_eps_isometry_comp
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:47:44.891511+00:00
-- url     : https://prove2.me/submissions/d87789e9-ce0c-4ca7-b592-7841dad6ff02

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

open GeomDL.Blueprint Filter

theorem solution :
    (∀ {X : Type} [PseudoMetricSpace X] (ε₁ ε₂ : ℝ) (τ₁ τ₂ : X → X),
      IsEpsIsometry ε₁ τ₁ → IsEpsIsometry ε₂ τ₂ → IsEpsIsometry (ε₁ + ε₂) (τ₁ ∘ τ₂)) ∧
    (∀ ε : ℝ, 0 < ε → ∃ τ : ℝ → ℝ, Continuous τ ∧ Function.Bijective τ ∧
      IsEpsIsometry ε τ ∧ ¬ IsEpsIsometry ε (τ ∘ τ)) := by
  refine ⟨fun ε₁ ε₂ τ₁ τ₂ h₁ h₂ u v => ?_, fun ε hε => ?_⟩
  · have a := h₁ (τ₂ u) (τ₂ v)
    have b := h₂ u v
    simp only [Function.comp]
    calc |dist (τ₁ (τ₂ u)) (τ₁ (τ₂ v)) - dist u v|
        = |(dist (τ₁ (τ₂ u)) (τ₁ (τ₂ v)) - dist (τ₂ u) (τ₂ v)) + (dist (τ₂ u) (τ₂ v) - dist u v)| := by
          ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ ε₁ + ε₂ := add_le_add a b
  · set c : ℝ → ℝ := fun x => max 0 (min x 1) with hc
    have c0 : ∀ x, 0 ≤ c x := fun x => le_max_left _ _
    have c1 : ∀ x, c x ≤ 1 := fun x => max_le zero_le_one (min_le_right _ _)
    have cm : Monotone c := fun x y h => max_le_max le_rfl (min_le_min h le_rfl)
    set τ : ℝ → ℝ := fun x => x + ε * c x with hτ
    have hcont : Continuous τ := by
      simp only [hτ, hc]; fun_prop
    have hsm : StrictMono τ := fun x y h => by
      simp only [hτ]; nlinarith [cm h.le]
    have hiso : IsEpsIsometry ε τ := by
      intro u v
      simp only [Real.dist_eq, hτ]
      rcases le_total v u with h | h
      · have := cm h
        have hd : 0 ≤ ε * (c u - c v) := mul_nonneg hε.le (by linarith)
        rw [abs_of_nonneg (show (0:ℝ) ≤ u + ε * c u - (v + ε * c v) by nlinarith),
          abs_of_nonneg (show (0:ℝ) ≤ u - v by linarith)]
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith [c1 u, c0 v]
      · have := cm h
        have hd : 0 ≤ ε * (c v - c u) := mul_nonneg hε.le (by linarith)
        rw [abs_of_nonpos (show u + ε * c u - (v + ε * c v) ≤ 0 by nlinarith),
          abs_of_nonpos (show u - v ≤ 0 by linarith)]
        rw [abs_of_nonneg (by nlinarith)]
        nlinarith [c1 v, c0 u]
    refine ⟨τ, hcont, ⟨hsm.injective, ?_⟩, hiso, ?_⟩
    · refine hcont.surjective ?_ ?_
      · exact tendsto_atTop_mono (fun x => show id x ≤ x + ε * c x by simp only [id]; nlinarith [c0 x]) tendsto_id
      · exact tendsto_atBot_mono (fun x => show x + ε * c x ≤ id x + ε by simp only [id]; nlinarith [c1 x])
          (tendsto_atBot_add_const_right _ ε tendsto_id)
    · intro h
      have := h 2 0
      have e0 : c 0 = 0 := by simp [hc]
      have e2 : c 2 = 1 := by simp [hc]
      have e3 : c (2 + ε) = 1 := by
        simp only [hc]; rw [min_eq_right (by linarith)]; norm_num
      have t0 : τ 0 = 0 := by simp only [hτ, e0]; ring
      have t2 : τ 2 = 2 + ε := by simp only [hτ, e2]; ring
      have t3 : τ (2 + ε) = 2 + 2 * ε := by simp only [hτ, e3]; ring
      simp only [Function.comp, Real.dist_eq, t0, t2, t3] at this
      rw [sub_zero, sub_zero, abs_of_pos (by linarith : (0:ℝ) < 2 + 2 * ε), abs_of_pos (by norm_num : (0:ℝ) < 2),
        show 2 + 2 * ε - 2 = 2 * ε by ring, abs_of_pos (by linarith)] at this
      linarith
