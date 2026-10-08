-- Prove2me | solution 1 for ImplicitCalculus.local_constraint_residual_bound
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-06T20:20:13.85916+00:00
-- url     : https://prove2.me/submissions/21909dfe-80f2-42c7-96b4-91d37541967d

import Theorems.Thm_ImplicitCalculus_local_level_retraction_bound
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.FDeriv.Basic

open Set Filter
open scoped Topology NNReal
set_option autoImplicit false

theorem solution {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : V → W) (D : V →L[ℝ] W) (y : V)
    (hF : HasStrictFDerivAt F D y) (hD : Function.Surjective D)
    (H : ℝ × V → U) (A : (ℝ × V) →L[ℝ] U) (t : ℝ) (T : Set ℝ)
    (hH : HasStrictFDerivAt H A (t,y))
    (hzero : ∀ s ∈ T, ∀ z, F z = F y → H (s,z) = 0) :
    ∃ C : ℝ≥0, ∀ᶠ p : ℝ × V in 𝓝 (t,y),
      p.1 ∈ T → ‖H p‖ ≤ C * ‖F p.2 - F y‖ := by
  obtain ⟨r, hrc, hry, C, hr⟩ := ImplicitCalculus.local_level_retraction_bound F D y hF hD
  obtain ⟨L, U, hU, hLip⟩ := hH.exists_lipschitzOnWith
  have hmap : Tendsto (fun p : ℝ × V => (p.1, r p.2)) (𝓝 (t,y)) (𝓝 (t,y)) := by
    simpa [hry] using continuousAt_fst.tendsto.prodMk_nhds
      (hrc.tendsto.comp continuousAt_snd.tendsto)
  refine ⟨L * C, ?_⟩
  filter_upwards [hU, hmap.eventually hU, continuousAt_snd.tendsto.eventually hr]
    with p hp hpr hrl
  intro ht
  calc
    ‖H p‖ = dist (H p) (H (p.1, r p.2)) := by
      rw [hzero p.1 ht (r p.2) hrl.1, dist_zero_right]
    _ ≤ L * dist p (p.1, r p.2) := hLip.dist_le_mul _ hp _ hpr
    _ = L * dist p.2 (r p.2) := by simp [Prod.dist_eq]
    _ ≤ L * (C * ‖F p.2 - F y‖) := mul_le_mul_of_nonneg_left hrl.2 L.2
    _ = (L * C : ℝ≥0) * ‖F p.2 - F y‖ := by simp [mul_assoc]
