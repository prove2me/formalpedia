-- Prove2me | solution 1 for GlobalInexactNewton.Backtracking.lemma_1_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:18:37.076714+00:00
-- url     : https://prove2.me/submissions/bc67d575-8208-44e9-bef7-b99c298cb91d

import Mathlib

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (F : E → E) (hF : ContDiff ℝ 1 F) (x : E) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ y ∈ Metric.ball x δ, ∀ z ∈ Metric.ball x δ,
      ‖F z - F y - fderiv ℝ F y (z - y)‖ ≤ ε * ‖z - y‖ := by
  have hs : HasStrictFDerivAt F (fderiv ℝ F x) x :=
    hF.contDiffAt.hasStrictFDerivAt (by simp)
  have h1 := hs.isLittleO.def (half_pos hε)
  rw [Metric.eventually_nhds_iff] at h1
  obtain ⟨δ1, hδ1, H1⟩ := h1
  have hc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  obtain ⟨δ2, hδ2, H2⟩ := Metric.continuous_iff.mp hc x (ε / 2) (half_pos hε)
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, ?_⟩
  intro y hy z hz
  rw [Metric.mem_ball] at hy hz
  have hy1 : dist y x < δ1 := lt_of_lt_of_le hy (min_le_left _ _)
  have hz1 : dist z x < δ1 := lt_of_lt_of_le hz (min_le_left _ _)
  have hy2 : dist y x < δ2 := lt_of_lt_of_le hy (min_le_right _ _)
  have hA := H1 (y := (z, y)) (by
    rw [Prod.dist_eq]
    exact max_lt (by simpa using hz1) (by simpa using hy1))
  have hB := H2 y hy2
  simp only [Real.norm_eq_abs, Pi.sub_apply] at hA
  rw [dist_eq_norm] at hB
  have hdec : F z - F y - fderiv ℝ F y (z - y) =
      (F z - F y - fderiv ℝ F x (z - y)) + (fderiv ℝ F x - fderiv ℝ F y) (z - y) := by
    simp
  have hC : ‖(fderiv ℝ F x - fderiv ℝ F y) (z - y)‖ ≤ ε / 2 * ‖z - y‖ := by
    calc ‖(fderiv ℝ F x - fderiv ℝ F y) (z - y)‖ ≤ ‖fderiv ℝ F x - fderiv ℝ F y‖ * ‖z - y‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε / 2 * ‖z - y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [norm_sub_rev]
          exact hB.le
  rw [hdec]
  calc ‖(F z - F y - fderiv ℝ F x (z - y)) + (fderiv ℝ F x - fderiv ℝ F y) (z - y)‖
      ≤ ‖F z - F y - fderiv ℝ F x (z - y)‖ + ‖(fderiv ℝ F x - fderiv ℝ F y) (z - y)‖ :=
        norm_add_le _ _
    _ ≤ ε / 2 * ‖z - y‖ + ε / 2 * ‖z - y‖ := add_le_add hA hC
    _ = ε * ‖z - y‖ := by ring
