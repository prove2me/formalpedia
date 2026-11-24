-- Prove2me | solution 1 for Kyprianou.Ch03.delayedNeighbourhoodClockBoundsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:42:59.242028+00:00
-- url     : https://prove2.me/submissions/c8c9887b-6e56-4ea7-a7c0-f331b5114bae

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Mathlib.Tactic.Positivity
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Omega : Type} (X : NNReal → Omega → ℝ) (B : Set ℝ) (a : NNReal)
    (T : ℕ → Omega → WithTop NNReal)
    (hT : ∀ n w, T n w = sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ Metric.thickening (1 / ((n : ℝ) + 1)) B})) (w : Omega) :
    Monotone (fun n => T n w) ∧
    (⨆ n, T n w) ≤ sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
      {t : NNReal | a ≤ t ∧ X t w ∈ B}) ∧
    (a : WithTop NNReal) ≤ ⨆ n, T n w := by
  constructor
  · intro n m hnm
    change T n w ≤ T m w
    rw [hT n w, hT m w]
    apply sInf_le_sInf
    rintro _ ⟨t, ⟨ha, ht⟩, rfl⟩
    refine ⟨t, ⟨ha, ?_⟩, rfl⟩
    exact Metric.thickening_mono (by gcongr <;> exact_mod_cast hnm) B ht
  constructor
  · apply iSup_le
    intro n
    rw [hT]
    apply sInf_le_sInf
    rintro _ ⟨t, ⟨ha, ht⟩, rfl⟩
    exact ⟨t, ⟨ha, Metric.self_subset_thickening (by positivity) B ht⟩, rfl⟩
  · apply le_trans _ (le_iSup (fun n => T n w) 0)
    rw [hT]
    apply le_sInf
    rintro _ ⟨t, ⟨ha, ht⟩, rfl⟩
    exact WithTop.coe_le_coe.mpr ha
