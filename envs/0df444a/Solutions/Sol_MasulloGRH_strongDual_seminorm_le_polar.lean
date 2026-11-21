-- Prove2me | solution 1 for MasulloGRH.strongDual_seminorm_le_polar
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:17:33.012985+00:00
-- url     : https://prove2.me/submissions/8e24e03d-45e1-4712-9eb1-0fae5c25d44b

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH Set Filter Topology

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsHLCS E)
    (p : Seminorm ℂ (StrongDual ℂ E)) (hp : Continuous p) :
    ∃ (B : Set E) (C : ℝ), Bornology.IsVonNBounded ℂ B ∧ 0 ≤ C ∧
      ∀ (f : StrongDual ℂ E) (r : ℝ), 0 ≤ r → (∀ x ∈ B, ‖f x‖ ≤ r) → p f ≤ C * r := by
  have hp1 : {f : StrongDual ℂ E | p f < 1} ∈ 𝓝 (0 : StrongDual ℂ E) :=
    (isOpen_lt hp continuous_const).mem_nhds (by simp)
  obtain ⟨⟨B, W⟩, ⟨hB, hW⟩, hsub⟩ := ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.1 hp1
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hW
  refine ⟨B, 2 / δ, hB, by positivity, fun f r hr hf => ?_⟩
  -- scaling `f` into the basic neighbourhood
  have key : ∀ t : ℝ, 0 < t → t * r < δ → t * p f < 1 := by
    intro t ht htr
    have hmem : ((t : ℂ) • f) ∈ {f : StrongDual ℂ E | p f < 1} := by
      apply hsub
      intro x hx
      apply hball
      rw [mem_ball_zero_iff]
      have h1 : ‖((t : ℂ) • f) x‖ = t * ‖f x‖ := by
        rw [smul_apply, norm_smul, Complex.norm_real,
          Real.norm_of_nonneg ht.le]
      rw [h1]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (hf x hx) ht.le) htr
    have h2 : p ((t : ℂ) • f) = t * p f := by
      rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg ht.le]
    rw [← h2]
    exact hmem
  by_cases hr0 : r = 0
  · subst hr0
    have hpf : p f ≤ 0 := by
      by_contra h
      push Not at h
      have h3 := key (1 / p f) (by positivity) (by simpa using hδ)
      rw [one_div, inv_mul_cancel₀ h.ne'] at h3
      exact lt_irrefl _ h3
    simpa using hpf
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have h3 := key (δ / (2 * r)) (by positivity) (by
      have : δ / (2 * r) * r = δ / 2 := by field_simp
      rw [this]; linarith)
    have h4 : p f * δ < 2 * r := by
      rw [div_mul_eq_mul_div, div_lt_one (by positivity)] at h3
      linarith
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
    linarith
