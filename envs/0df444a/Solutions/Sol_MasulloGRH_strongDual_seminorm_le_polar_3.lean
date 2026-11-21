-- Prove2me | solution 3 for MasulloGRH.strongDual_seminorm_le_polar
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:19:58.811979+00:00
-- url     : https://prove2.me/submissions/352ba838-6d5a-4ae0-9796-539c342a8c62

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Topology Set

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : MasulloGRH.IsHLCS E)
    (p : Seminorm ℂ (StrongDual ℂ E)) (hp : Continuous p) :
    ∃ (B : Set E) (C : ℝ), Bornology.IsVonNBounded ℂ B ∧ 0 ≤ C ∧
      ∀ (f : StrongDual ℂ E) (r : ℝ), 0 ≤ r → (∀ x ∈ B, ‖f x‖ ≤ r) → p f ≤ C * r := by
  have hU : {f : StrongDual ℂ E | p f < 1} ∈ 𝓝 (0 : StrongDual ℂ E) := by
    have := hp.tendsto 0; rw [map_zero] at this
    exact this (gt_mem_nhds one_pos)
  obtain ⟨⟨B, V⟩, ⟨hB, hV⟩, hsub⟩ :=
    (ContinuousLinearMap.hasBasis_nhds_zero (σ := RingHom.id ℂ) (E := E) (F := ℂ)).mem_iff.mp hU
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨B, 2 / ε, hB, by positivity, fun f r hr hfB => ?_⟩
  -- for every s > r, p f ≤ 2 s / ε
  have key : ∀ s : ℝ, r < s → p f ≤ 2 / ε * s := by
    intro s hs
    have hs0 : 0 < s := lt_of_le_of_lt hr hs
    set t : ℝ := ε / (2 * s) with ht
    have ht0 : 0 < t := by positivity
    have hmem : (t : ℂ) • f ∈ {f : StrongDual ℂ E | p f < 1} := by
      apply hsub
      intro x hx
      apply hεV
      simp only [Metric.mem_ball, dist_zero_right, smul_apply, norm_smul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      calc t * ‖f x‖ ≤ t * r := mul_le_mul_of_nonneg_left (hfB x hx) ht0.le
        _ < t * (2 * s) := by nlinarith
        _ = ε := by rw [ht]; field_simp
    simp only [mem_ofPred_eq, map_smul_eq_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht0] at hmem
    have : p f < 1 / t := by rw [lt_div_iff₀ ht0]; linarith
    calc p f ≤ 1 / t := this.le
      _ = 2 / ε * s := by rw [ht]; field_simp
  have hC : 0 < 2 / ε := by positivity
  refine le_of_forall_pos_lt_add fun δ hδ => ?_
  have := key (r + δ / (2 * (2 / ε))) (by have : 0 < δ / (2 * (2 / ε)) := by positivity
                                          linarith)
  have e : 2 / ε * (r + δ / (2 * (2 / ε))) = 2 / ε * r + δ / 2 := by field_simp
  linarith
