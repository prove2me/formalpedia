-- Prove2me | solution 1 for MilnorDynamics.exists_sphere_ne_zero_of_analytic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T23:38:06.391+00:00
-- url     : https://prove2.me/submissions/d1b50421-61ae-4ff5-a865-f3e48472776c

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set
open MilnorDynamics

/-- Repaired variant: the two rewrites are performed on separate goals, and the
union membership is split by `simp only [Set.mem_union]` rather than by
projecting `Set.mem_union`, whose set arguments are explicit. -/
theorem solution (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (G : ℂ → ℂ) (hG : AnalyticOnNhd ℂ G U) (z0 : ℂ) (hz0 : z0 ∈ U)
    (hne : ∃ w ∈ U, G w ≠ 0) :
    ∃ r > 0, Metric.closedBall z0 r ⊆ U ∧ ∀ z ∈ Metric.sphere z0 r, G z ≠ 0 := by
  rcases hG.eqOn_zero_or_eventually_ne_zero_of_preconnected hUc.isPreconnected with hEq | hEv
  · obtain ⟨w, hwU, hw⟩ := hne
    exact absurd (hEq hwU) hw
  · have hmem : ({x : ℂ | G x ≠ 0} ∪ Uᶜ) ∈ nhdsWithin z0 ({z0}ᶜ : Set ℂ) :=
      (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hEv) z0 hz0
    obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhdsWithin_iff.mp hmem
    obtain ⟨ρ, hρpos, hρU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz0)
    have hltρ : min (ε / 2) (ρ / 2) < ρ := by
      have := min_le_right (ε / 2) (ρ / 2)
      linarith
    have hltε : min (ε / 2) (ρ / 2) < ε := by
      have := min_le_left (ε / 2) (ρ / 2)
      linarith
    have hrpos : 0 < min (ε / 2) (ρ / 2) :=
      lt_min (by linarith) (by linarith)
    refine ⟨min (ε / 2) (ρ / 2), hrpos, ?_, ?_⟩
    · intro z hz
      exact hρU (Metric.closedBall_subset_ball hltρ hz)
    · intro z hz
      have hzball : z ∈ Metric.ball z0 ε := by
        have h := hz
        rw [Metric.mem_sphere] at h
        rw [Metric.mem_ball]
        linarith
      have hzne : z ≠ z0 := by
        have h := hz
        rw [Metric.mem_sphere] at h
        intro hh
        rw [hh, dist_self] at h
        linarith
      have hzU : z ∈ U :=
        hρU (Metric.closedBall_subset_ball hltρ (Metric.sphere_subset_closedBall hz))
      have hmemz := hεsub ⟨hzball, by simpa using hzne⟩
      simp only [Set.mem_union] at hmemz
      rcases hmemz with hgood | hbad
      · exact hgood
      · exact absurd hzU hbad
