-- Prove2me | solution 3 for NonsmoothNewton.Global.limit_is_root
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:11:24.973238+00:00
-- url     : https://prove2.me/submissions/df5fa10b-9985-44c1-b0b6-9d9b56602d42

import Mathlib
import Definitions.Def_NonsmoothNewton_Global_dirDeriv
import Definitions.Def_NonsmoothNewton_Global_clarkeJac
import Definitions.Def_NonsmoothNewton_Global_SemismoothAt
import Definitions.Def_NonsmoothNewton_Global_IsNewtonRun



namespace NonsmoothNewton.Global

open Filter Topology

lemma clarke_local_bound {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (y : EuclideanSpace ℝ (Fin n)) :
    ∃ ε > 0, ∃ K : ℝ, ∀ x ∈ Metric.ball y ε, ∀ V ∈ clarkeJac F x, ‖V‖ ≤ K := by
  obtain ⟨K, t, ht, hlip⟩ := hF y
  obtain ⟨e, he, hball⟩ := Metric.mem_nhds_iff.1 ht
  refine ⟨e / 2, by positivity, K, ?_⟩
  intro x hx V hV
  have hsub : Metric.ball x (e / 2) ⊆ t := by
    intro z hz
    apply hball
    rw [Metric.mem_ball] at *
    calc dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      _ < e / 2 + e / 2 := add_lt_add hz hx
      _ = e := by ring
  have hb : bJac F x ⊆ Metric.closedBall 0 (K : ℝ) := by
    rintro W ⟨u, hu, -, hW⟩
    have hev : ∀ᶠ k in atTop, u k ∈ Metric.ball x (e / 2) :=
      hu (Metric.ball_mem_nhds x (by positivity))
    have hev2 : ∀ᶠ k in atTop, ‖fderiv ℝ F (u k)‖ ≤ K := by
      filter_upwards [hev] with k hk
      exact norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hk) (hlip.mono hsub)
    rw [mem_closedBall_zero_iff]
    exact le_of_tendsto ((continuous_norm.tendsto W).comp hW) hev2
  have := convexHull_min hb (convex_closedBall 0 (K : ℝ)) hV
  simpa using this

lemma clarke_compact_bound {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (hF : LocallyLipschitz F)
    (s : Set (EuclideanSpace ℝ (Fin n))) (hs : IsCompact s) :
    ∃ K : ℝ, ∀ x ∈ s, ∀ V ∈ clarkeJac F x, ‖V‖ ≤ K := by
  refine hs.induction_on (p := fun s => ∃ K : ℝ, ∀ x ∈ s, ∀ V ∈ clarkeJac F x, ‖V‖ ≤ K)
    ⟨0, by simp⟩ ?_ ?_ ?_
  · rintro s t hst ⟨K, hK⟩
    exact ⟨K, fun x hx => hK x (hst hx)⟩
  · rintro s t ⟨K1, h1⟩ ⟨K2, h2⟩
    refine ⟨max K1 K2, ?_⟩
    rintro x (hx | hx) V hV
    · exact (h1 x hx V hV).trans (le_max_left _ _)
    · exact (h2 x hx V hV).trans (le_max_right _ _)
  · intro y _
    obtain ⟨ε, hε, K, hK⟩ := clarke_local_bound F hF y
    exact ⟨Metric.ball y ε, mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds y hε), K, hK⟩

theorem limit_is_root_core {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hF : LocallyLipschitz F)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hrun : IsNewtonRun F x V) (hS : ∀ k, x k ∈ Metric.closedBall x0 r)
    (xstar : EuclideanSpace ℝ (Fin n)) (hlim : Tendsto x atTop (𝓝 xstar)) :
    (∃ C : ℝ, ∀ k, ‖V k‖ ≤ C) ∧ xstar ∈ Metric.closedBall x0 r ∧ F xstar = 0 := by
  obtain ⟨C, hC⟩ := clarke_compact_bound F hF _ (isCompact_closedBall x0 r)
  have hVb : ∀ k, ‖V k‖ ≤ C := fun k => hC _ (hS k) _ (hrun k).1
  refine ⟨⟨C, hVb⟩, (Metric.isClosed_closedBall).mem_of_tendsto hlim (Eventually.of_forall hS), ?_⟩
  have hcont : Continuous F := hF.continuous
  have h1 : Tendsto (fun k => F (x k)) atTop (𝓝 (F xstar)) := (hcont.tendsto _).comp hlim
  have hdiff : Tendsto (fun k => x (k + 1) - x k) atTop (𝓝 0) := by
    have := ((tendsto_add_atTop_iff_nat 1).2 hlim).sub hlim
    simpa using this
  have h2 : Tendsto (fun k => F (x k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hd := (tendsto_zero_iff_norm_tendsto_zero.1 hdiff).const_mul C
    rw [mul_zero] at hd
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hd
    have := (hrun k).2
    calc ‖F (x k)‖ = ‖V k (x (k + 1) - x k)‖ := by rw [this, norm_neg]
      _ ≤ ‖V k‖ * ‖x (k + 1) - x k‖ := (V k).le_opNorm _
      _ ≤ C * ‖x (k + 1) - x k‖ := mul_le_mul_of_nonneg_right (hVb k) (norm_nonneg _)
  exact tendsto_nhds_unique h1 h2

end NonsmoothNewton.Global

open NonsmoothNewton.Global
open Filter Topology

theorem solution {n : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (x0 : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hF : LocallyLipschitz F)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (V : ℕ → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hrun : IsNewtonRun F x V) (hS : ∀ k, x k ∈ Metric.closedBall x0 r)
    (xstar : EuclideanSpace ℝ (Fin n)) (hlim : Tendsto x atTop (𝓝 xstar)) :
    (∃ C : ℝ, ∀ k, ‖V k‖ ≤ C) ∧ xstar ∈ Metric.closedBall x0 r ∧ F xstar = 0 := by
  exact limit_is_root_core F x0 r hF x V hrun hS xstar hlim
