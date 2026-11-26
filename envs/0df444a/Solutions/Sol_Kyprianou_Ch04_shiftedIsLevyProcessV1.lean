-- Prove2me | solution 1 for Kyprianou.Ch04.shiftedIsLevyProcessV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:37:39.349942+00:00
-- url     : https://prove2.me/submissions/a6a36c62-c022-41eb-97a5-c051aced94c4

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Deterministic time translation and recentering preserves the Levy process axioms. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℝ≥0 → Ω → ℝ) (hX : IsLevyProcess X P) (s : ℝ≥0) :
    IsLevyProcess (fun t ω => X (s + t) ω - X s ω) P := by
  constructor
  · funext ω
    simp
  · intro n t ht
    let u : Fin (n + 1) → ℝ≥0 := fun k => s + t k
    have hu : Monotone u := fun i j hij => add_le_add_right (ht hij) s
    have hi := hX.indep_increments n u hu
    convert hi using 1
    funext k ω
    simp only [increment, u]
    ring
  · intro a b
    have h := (hX.stationary_increments (s + a) b).trans
      (hX.stationary_increments s b).symm
    convert h using 1
    · funext ω
      simp only [increment, add_assoc]
      ring
    · funext ω
      simp [increment]
  · filter_upwards [hX.cadlag_ae] with ω hc
    intro t
    have hA : Continuous (fun u : ℝ≥0 => s + u) := continuous_const.add continuous_id
    have hr : Tendsto (fun u : ℝ≥0 => s + u) (nhdsWithin t (Ici t))
        (nhdsWithin (s + t) (Ici (s + t))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hA.continuousAt.continuousWithinAt, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact add_le_add_right hu s
    have hl : Tendsto (fun u : ℝ≥0 => s + u) (nhdsWithin t (Iio t))
        (nhdsWithin (s + t) (Iio (s + t))) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hA.continuousAt.continuousWithinAt, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact add_lt_add_right hu s
    refine ⟨((hc (s + t)).1.tendsto.comp hr).sub tendsto_const_nhds, ?_⟩
    obtain ⟨l, hL⟩ := (hc (s + t)).2
    exact ⟨l - X s ω, (hL.comp hl).sub tendsto_const_nhds⟩
