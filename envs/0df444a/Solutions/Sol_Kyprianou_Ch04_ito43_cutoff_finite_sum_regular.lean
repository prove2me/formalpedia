-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_cutoff_finite_sum_regular
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:11:47.524806+00:00
-- url     : https://prove2.me/submissions/d3983625-f7cf-492c-8e73-ca63b1f1430a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution {ι : Type} (S : Finset ι) (F : ι → NNReal → ℝ) (T : NNReal)
    (hR : ∀ i ∈ S, ∀ t, ContinuousWithinAt (F i) (Ici t) t)
    (hB : ∀ i ∈ S, ∃ M : ℝ, ∀ t ≤ T, |F i t| ≤ M) :
    (∀ t, ContinuousWithinAt (fun s => ∑ i ∈ S, F i s) (Ici t) t) ∧
      ∃ M : ℝ, ∀ t ≤ T, |∑ i ∈ S, F i t| ≤ M := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨fun t => by simpa using (continuousWithinAt_const (b := (0:ℝ))),
      0,fun t ht => by simp⟩
  | @insert i S hi ih =>
    have hRi := hR i (Finset.mem_insert_self i S)
    obtain ⟨Mi,hMi⟩ := hB i (Finset.mem_insert_self i S)
    obtain ⟨hr, M,hM⟩ := ih
      (fun j hj => hR j (Finset.mem_insert_of_mem hj))
      (fun j hj => hB j (Finset.mem_insert_of_mem hj))
    refine ⟨?_,Mi+M,?_⟩
    · intro t
      have heq : (fun s => ∑ j ∈ insert i S, F j s) =
          F i + (fun s => ∑ j ∈ S, F j s) := by
        funext s
        simp only [Finset.sum_insert hi,Pi.add_apply]
      rw [heq]
      exact (hRi t).add (hr t)
    · intro t ht
      rw [Finset.sum_insert hi]
      exact (abs_add_le _ _).trans (add_le_add (hMi t ht) (hM t ht))
