-- Prove2me | solution 2 for MasulloGRH.strongDual_evaluation_seminorm
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:18:12.102491+00:00
-- url     : https://prove2.me/submissions/4c9579eb-fef7-46cd-9cb4-6283e3c3124e

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Topology Set

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : MasulloGRH.IsHLCS E)
    (y : ℕ → E) (hy : Bornology.IsVonNBounded ℂ (Set.range y)) :
    ∃ (q : Seminorm ℂ (StrongDual ℂ E)) (φ : ℕ → StrongDual ℂ (StrongDual ℂ E)),
      Continuous q ∧ (∀ n f, φ n f = f (y n)) ∧ ∀ n (f : StrongDual ℂ E), ‖f (y n)‖ ≤ q f := by
  -- evaluation as linear maps
  let ev : ℕ → (StrongDual ℂ E →ₗ[ℂ] ℂ) := fun n =>
    { toFun := fun f => f (y n), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let P : ℕ → Seminorm ℂ (StrongDual ℂ E) := fun n => (normSeminorm ℂ ℂ).comp (ev n)
  have hPn : ∀ n f, P n f = ‖f (y n)‖ := fun n f => rfl
  -- each f is bounded on range y
  have hbd : ∀ f : StrongDual ℂ E, ∃ M, ∀ n, ‖f (y n)‖ ≤ M := by
    intro f
    have hV : f ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : E) :=
      f.continuous.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds (0:ℂ) one_pos)
    obtain ⟨r, hr, h⟩ := (hy hV).exists_pos
    refine ⟨r, fun n => ?_⟩
    have := h (r : ℂ) (by simp [abs_of_pos hr]) (mem_range_self n)
    obtain ⟨v, hv, hvy⟩ := Set.mem_smul_set.mp this
    rw [← hvy, map_smul, norm_smul]
    simp only [mem_preimage, Metric.mem_ball, dist_zero_right] at hv
    have : ‖(r:ℂ)‖ = r := by simp [abs_of_pos hr]
    rw [this]; nlinarith [norm_nonneg (f v)]
  have hB : BddAbove (range P) := by
    rw [Seminorm.bddAbove_range_iff]
    intro f; obtain ⟨M, hM⟩ := hbd f
    exact ⟨M, by rintro _ ⟨n, rfl⟩; exact hM n⟩
  let q := ⨆ n, P n
  have hqa : ∀ f, q f = ⨆ n, ‖f (y n)‖ := fun f => Seminorm.iSup_apply hB
  have hle : ∀ n f, ‖f (y n)‖ ≤ q f := by
    intro n f; rw [hqa]
    obtain ⟨M, hM⟩ := hbd f
    exact le_ciSup ⟨M, by rintro _ ⟨m, rfl⟩; exact hM m⟩ n
  have hqc : Continuous q := by
    have hball : Metric.ball (0:ℂ) (1/2) ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds _ (by norm_num)
    have hev := ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hy hball
    refine Seminorm.continuous (r := 1) (Filter.mem_of_superset hev ?_)
    intro f hf
    rw [Seminorm.mem_ball_zero, hqa]
    have : ∀ n, ‖f (y n)‖ ≤ 1/2 := fun n => by
      have := hf (mem_range_self n); simp only [Metric.mem_ball, dist_zero_right] at this
      exact this.le
    calc (⨆ n, ‖f (y n)‖) ≤ 1/2 := ciSup_le this
      _ < 1 := by norm_num
  -- continuous linear evaluations
  have hφc : ∀ n, Continuous (ev n) := by
    intro n
    refine continuous_of_continuousAt_zero (ev n).toAddMonoidHom ?_
    rw [ContinuousAt, map_zero]
    rw [Metric.tendsto_nhds]
    intro ε hε
    have : ∀ᶠ f in 𝓝 (0 : StrongDual ℂ E), q f < ε := by
      have := hqc.tendsto 0; rw [map_zero] at this
      exact this.eventually (gt_mem_nhds hε)
    filter_upwards [this] with f hf
    simp only [dist_zero_right]
    exact lt_of_le_of_lt (hle n f) hf
  exact ⟨q, fun n => ⟨ev n, hφc n⟩, hqc, fun n f => rfl, hle⟩
