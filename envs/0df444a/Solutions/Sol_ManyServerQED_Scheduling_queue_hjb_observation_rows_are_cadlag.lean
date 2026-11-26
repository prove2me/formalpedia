-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_observation_rows_are_cadlag
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:40:58.549077+00:00
-- url     : https://prove2.me/submissions/3ab40a84-1091-4e1e-a3e5-bcfd03477f9a

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_controlled_queue_state_and_effective_noise_are_cadlag
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
private theorem cadlag_of_continuousOn {f : ℝ → ℝ} (h : ContinuousOn f (Ici (0:ℝ))) :
    IsCadlag f := by
  refine ⟨fun t ht => (h t ht).mono (fun s hs => ht.trans hs),fun t ht => ⟨f t,?_⟩⟩
  have ht' : Ici (0:ℝ) ∈ 𝓝 t := Ici_mem_nhds ht
  exact ((h t ht.le).continuousAt ht').tendsto.mono_left nhdsWithin_le_nhds


set_option maxHeartbeats 1300000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (hC : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n)) :
    ∀ n, 1 ≤ n → ∀ ω i, IsCadlag (fun t =>
      queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ n ω t i) := by
  let Z := queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ
  have hH := queue_hjb_row_integral_paths M Lt γ ϱ mL hA2 u0 hu0 f hH X Ψ X0 hC hWork
  intro n hn ω i
  change IsCadlag (fun t => Z n ω t i)
  have hIt := hH.1 n hn ω
  cases i using Fin.addCases with
  | right i =>
    fin_cases i
    · simpa only [Z,queueHJBObservation,Fin.append_right,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using
        cadlag_of_continuousOn hIt.2.1
    · simpa only [Z,queueHJBObservation,Fin.append_right,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using
        cadlag_of_continuousOn hIt.2.2.1
  | left i =>
    cases i using Fin.addCases with
    | right i =>
      simpa only [Z,queueHJBObservation,Fin.append_left,Fin.append_right] using
        cadlag_of_continuousOn (hIt.1 i)
    | left i =>
      cases i using Fin.addCases with
      | left i =>
        simpa only [Z,queueHJBObservation,Fin.append_left] using
          (controlled_queue_state_and_effective_noise_are_cadlag M n hn (X0 n) (X n) (Ψ n) (hC n hn).controlled ω i).1
      | right i =>
        simpa only [Z,queueHJBObservation,Fin.append_left,Fin.append_right] using
          (controlled_queue_state_and_effective_noise_are_cadlag M n hn (X0 n) (X n) (Ψ n) (hC n hn).controlled ω i).2
