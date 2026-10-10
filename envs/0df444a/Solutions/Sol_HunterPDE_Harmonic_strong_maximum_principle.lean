-- Prove2me | solution 1 for HunterPDE.Harmonic.strong_maximum_principle
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-09T15:55:20.389286+00:00
-- url     : https://prove2.me/submissions/73cf493c-b82f-41e7-96b4-cc5471e23511

import Theorems.Thm_HunterPDE_Harmonic_mean_value_inequality
import Theorems.Thm_MeasureTheory_eqOn_of_le_setAverage
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Connected.Basic

open MeasureTheory Set HunterPDE.Harmonic Topology
set_option autoImplicit false

theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hΩ : IsOpen Ω) (hconn : IsPreconnected Ω)
    (hu : IsSubharmonicOn Ω u) (hmax : ∃ x₀ ∈ Ω, ∀ x ∈ Ω, u x ≤ u x₀) :
    ∃ c : ℝ, ∀ x ∈ Ω, u x = c := by
  obtain ⟨x₀, hx₀, hmax⟩ := hmax
  refine ⟨u x₀, ?_⟩
  by_cases hn : n = 0
  · subst n
    intro x _
    exact congrArg u (Subsingleton.elim x x₀)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let F : Set (EuclideanSpace ℝ (Fin n)) := {x | x ∈ Ω ∧ u x = u x₀}
  have hF : IsOpen F := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.mp (hΩ.mem_nhds hx.1)
    have hr : 0 < ε / 2 := half_pos hε
    have hball : Metric.closedBall x (ε / 2) ⊆ Ω :=
      (Metric.closedBall_subset_ball (half_lt_self hε)).trans hb
    have hc := hu.1.continuousOn.mono hball
    have hi : IntegrableOn u (Metric.ball x (ε / 2)) :=
      (hc.integrableOn_compact (isCompact_closedBall x (ε / 2))).mono_set
        Metric.ball_subset_closedBall
    have hav := ((mean_value_inequality hnpos hΩ hr hball).1 hu).1
    have heq := MeasureTheory.eqOn_of_le_setAverage Metric.isOpen_ball
      (measure_ball_lt_top.ne) (hu.1.continuousOn.mono
        (Metric.ball_subset_closedBall.trans hball)) hi
      (fun y hy => (hmax y (hball (Metric.ball_subset_closedBall hy))).trans
        (hx.2 ▸ hav))
    have hcentre := heq (Metric.mem_ball_self hr)
    apply Filter.mem_of_superset (Metric.ball_mem_nhds x hr)
    intro y hy
    exact ⟨hball (Metric.ball_subset_closedBall hy), (heq hy).trans (hcentre.symm.trans hx.2)⟩
  obtain ⟨C, hC, hCe⟩ := (continuousOn_iff_isClosed.mp hu.1.continuousOn)
    {u x₀} isClosed_singleton
  have hsubset : Ω ⊆ F := hconn.subset_of_closure_inter_subset hF
    ⟨x₀, hx₀, hx₀, rfl⟩ (by
      intro x hx
      have hFC : F ⊆ C := by
        intro y hy
        have : y ∈ u ⁻¹' {u x₀} ∩ Ω := ⟨hy.2, hy.1⟩
        rw [hCe] at this
        exact this.1
      have hxC := (closure_minimal hFC hC) hx.1
      have : x ∈ u ⁻¹' {u x₀} ∩ Ω := by
        rw [hCe]
        exact ⟨hxC, hx.2⟩
      exact ⟨hx.2, this.1⟩)
  exact fun x hx => (hsubset hx).2
