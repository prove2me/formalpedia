-- Prove2me | solution 1 for NonsmoothLojasiewicz.Continuous.crit_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:11:41.562651+00:00
-- url     : https://prove2.me/submissions/2de5eb6c-0d07-4bc6-a4d4-30d5dcfaa4aa

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope

open Filter Topology
open scoped ENNReal

open NonsmoothLojasiewicz.Continuous in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hdom : IsClosed {x | f x ≠ ⊤}) (hcont : ContinuousOn f {x | f x ≠ ⊤}) :
    IsClosed (crit f) := by
  refine IsSeqClosed.isClosed ?_
  intro u x hu hux
  have hu' : ∀ k, f (u k) ≠ ⊤ ∧ ∃ xs vs : ℕ → EuclideanSpace ℝ (Fin n),
      Tendsto xs atTop (𝓝 (u k)) ∧ Tendsto (fun t => f (xs t)) atTop (𝓝 (f (u k))) ∧
      Tendsto vs atTop (𝓝 0) ∧
      ∀ t, NonconvexSplitting.Shared.IsRegularSubgrad f (xs t) (vs t) := fun k => hu k
  have hxdom : f x ≠ ⊤ :=
    hdom.mem_of_tendsto hux (Eventually.of_forall fun k => (hu' k).1)
  have key : ∀ k : ℕ, ∃ y w : EuclideanSpace ℝ (Fin n), dist y (u k) < 1 / ((k : ℝ) + 1) ∧
      ‖w‖ < 1 / ((k : ℝ) + 1) ∧ NonconvexSplitting.Shared.IsRegularSubgrad f y w := by
    intro k
    obtain ⟨_, xs, vs, hxs, -, hvs, hreg⟩ := hu' k
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have h1 := (Metric.tendsto_atTop.mp hxs) _ hpos
    have h2 := (Metric.tendsto_atTop.mp hvs) _ hpos
    obtain ⟨N1, hN1⟩ := h1
    obtain ⟨N2, hN2⟩ := h2
    refine ⟨xs (max N1 N2), vs (max N1 N2), hN1 _ (le_max_left _ _), ?_, hreg _⟩
    have := hN2 (max N1 N2) (le_max_right N1 N2)
    rwa [dist_zero_right] at this
  choose y w hy hw hreg using key
  have hy_lim : Tendsto y atTop (𝓝 x) := by
    have h1 : Tendsto (fun k => dist (y k) (u k)) atTop (𝓝 0) :=
      squeeze_zero (fun _ => dist_nonneg) (fun k => (hy k).le)
        tendsto_one_div_add_atTop_nhds_zero_nat
    rw [tendsto_iff_dist_tendsto_zero]
    have h2 := tendsto_iff_dist_tendsto_zero.mp hux
    refine squeeze_zero (fun _ => dist_nonneg) (fun k => dist_triangle _ (u k) _) ?_
    simpa using h1.add h2
  have hw_lim : Tendsto w atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    exact squeeze_zero (fun _ => norm_nonneg _) (fun k => (hw k).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hydom : ∀ k, y k ∈ {x | f x ≠ ⊤} := fun k => (hreg k).1
  have hfy : Tendsto (fun k => f (y k)) atTop (𝓝 (f x)) :=
    (hcont x hxdom).tendsto.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hy_lim, Eventually.of_forall hydom⟩)
  show (0 : EuclideanSpace ℝ (Fin n)) ∈ NonconvexSplitting.Shared.LimitingSubdiff f x
  exact ⟨hxdom, y, w, hy_lim, hfy, hw_lim, hreg⟩
