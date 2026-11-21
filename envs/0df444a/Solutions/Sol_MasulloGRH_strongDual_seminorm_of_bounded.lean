-- Prove2me | solution 1 for MasulloGRH.strongDual_seminorm_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:33:26.391205+00:00
-- url     : https://prove2.me/submissions/48587bef-4399-4379-8a95-c841835e9657

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open Topology Set

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : MasulloGRH.IsHLCS E) (B : Set E) (hBd : Bornology.IsVonNBounded ℂ B) :
    ∃ p : Seminorm ℂ (StrongDual ℂ E), Continuous p ∧
      ∀ (f : StrongDual ℂ E), ∀ x ∈ B, ‖f x‖ ≤ p f := by
  -- evaluation as linear maps
  let ev : ↥B → (StrongDual ℂ E →ₗ[ℂ] ℂ) := fun n =>
    { toFun := fun f => f (n : E), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let P : ↥B → Seminorm ℂ (StrongDual ℂ E) := fun n => (normSeminorm ℂ ℂ).comp (ev n)
  have hPn : ∀ n f, P n f = ‖f (n : E)‖ := fun n f => rfl
  -- each f is bounded on range y
  have hbd : ∀ f : StrongDual ℂ E, ∃ M, ∀ n : ↥B, ‖f (n : E)‖ ≤ M := by
    intro f
    have hV : f ⁻¹' Metric.ball 0 1 ∈ 𝓝 (0 : E) :=
      f.continuous.continuousAt.preimage_mem_nhds (by simpa using Metric.ball_mem_nhds (0:ℂ) one_pos)
    obtain ⟨r, hr, h⟩ := (hBd hV).exists_pos
    refine ⟨r, fun n => ?_⟩
    have := h (r : ℂ) (by simp [abs_of_pos hr]) n.2
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
  have hqa : ∀ f, q f = ⨆ n : ↥B, ‖f (n : E)‖ := fun f => Seminorm.iSup_apply hB
  have hle : ∀ (n : ↥B) f, ‖f (n : E)‖ ≤ q f := by
    intro n f; rw [hqa]
    obtain ⟨M, hM⟩ := hbd f
    exact le_ciSup ⟨M, by rintro _ ⟨m, rfl⟩; exact hM m⟩ n
  have hqc : Continuous q := by
    have hball : Metric.ball (0:ℂ) (1/2) ∈ 𝓝 (0:ℂ) := Metric.ball_mem_nhds _ (by norm_num)
    have hev := ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hBd hball
    refine Seminorm.continuous (r := 1) (Filter.mem_of_superset hev ?_)
    intro f hf
    rw [Seminorm.mem_ball_zero, hqa]
    have : ∀ n : ↥B, ‖f (n : E)‖ ≤ 1/2 := fun n => by
      have := hf n.2; simp only [Metric.mem_ball, dist_zero_right] at this
      exact this.le
    calc (⨆ n : ↥B, ‖f (n : E)‖) ≤ 1/2 := Real.iSup_le this (by norm_num)
      _ < 1 := by norm_num
  exact ⟨q, hqc, fun f x hx => hle ⟨x, hx⟩ f⟩
