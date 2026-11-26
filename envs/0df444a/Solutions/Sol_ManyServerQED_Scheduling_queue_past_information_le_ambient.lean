-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_past_information_le_ambient
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:52:50.111633+00:00
-- url     : https://prove2.me/submissions/58eb80da-0a67-4869-a79c-a3a9a2cacb3a

import Theorems.Thm_ManyServerQED_Scheduling_queue_past_generators_are_ambient_measurable
open Filter Topology MeasureTheory ProbabilityTheory Set
open scoped NNReal
open ManyServerQED.Scheduling

set_option maxHeartbeats 1650000 in
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (X₀ : Fin k → ℕ)
    (X Ψ : Ω → ℝ → Fin k → ℝ) (hC : M.IsSCP n X₀ X Ψ)
    (T : ℝ≥0) : M.pastInfo n X Ψ T ≤ mΩ := by
  refine iSup_le (fun i => iSup_le (fun t => iSup_le (fun ht => ?_)))
  obtain ⟨hA,hS,hR,hΦ,hP,hX⟩ := queue_past_generators_are_ambient_measurable M n X₀ X Ψ hC i t ht.1
  exact sup_le (sup_le (sup_le (sup_le (sup_le hA.comap_le hS.comap_le) hR.comap_le)
    hΦ.comap_le) hP.comap_le) hX.comap_le
