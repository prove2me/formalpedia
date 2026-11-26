-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_coupled_paths_have_joint_observation_limits
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:37:17.567633+00:00
-- url     : https://prove2.me/submissions/7f9cdb24-90ad-46e0-8edd-5fb2a88677dd

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_weak_convergence_from_coupled_observations

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 1300000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : ℕ → Ω → ℝ → Fin (k+k+k+2) → ℝ} {s : ℕ → ℕ}
    (d : QueueHJBPathSubseq P Z s) :
    letI := d.isProb
    ∃ N : ℕ, ∀ (m : ℕ) (τ : Fin m → ℝ≥0),
      TendstoInDistribution
        (fun j ω l => Z (s (d.r (j+N))) ω (τ l)) atTop
        (fun ω l => d.limit ω (τ l)) (fun _ => P) d.Q := by
  let : IsProbabilityMeasure d.Q := d.isProb
  obtain ⟨N,hN⟩ := eventually_atTop.1 d.row_law
  refine ⟨N,fun m τ => ?_⟩
  let ζ (j : ℕ) (ω : Ω) (t : ℝ≥0) := Z (s (d.r (j+N))) ω t
  let q (j : ℕ) (ω : d.Ω') (t : ℝ≥0) := d.row (j+N) ω t
  let h (p : ℝ≥0 → Fin (k+k+k+2) → ℝ) (l : Fin m) := p (τ l)
  have hMe : Measurable h := measurable_pi_lambda _ (fun l => measurable_pi_apply (τ l))
  have hLaw (j : ℕ) : IdentDistrib (ζ j) (q j) P d.Q :=
    (hN (j+N) (by omega)).symm
  have hLm : AEMeasurable (fun ω l => d.limit ω (τ l)) d.Q :=
    aemeasurable_pi_lambda _ (fun l => (d.limit_meas (τ l)).aemeasurable)
  refine weak_convergence_from_coupled_observations ζ q hLaw h hMe _ hLm ?_
  filter_upwards [d.convergence] with ω hω
  apply tendsto_pi_nhds.2
  intro l
  apply tendsto_pi_nhds.2
  intro i
  have hSup := (hω (τ l:ℝ) (τ l).2).comp (tendsto_add_atTop_nat N)
  apply Metric.tendsto_nhds.2
  intro ε hε
  filter_upwards [(tendsto_order.1 hSup).2 _ (ENNReal.ofReal_pos.2 hε)] with j hj
  have hFin : |d.row (j+N) ω (τ l) i - d.limit ω (τ l) i| ≤
      ∑ q, |d.row (j+N) ω (τ l) q-d.limit ω (τ l) q| :=
    Finset.single_le_sum (f := fun q => |d.row (j+N) ω (τ l) q-d.limit ω (τ l) q|)
      (fun q _ => abs_nonneg _) (Finset.mem_univ i)
  have hStep : ENNReal.ofReal |d.row (j+N) ω (τ l) i-d.limit ω (τ l) i| ≤
      supDist (d.row (j+N) ω) (d.limit ω) (τ l:ℝ) :=
    (ENNReal.ofReal_le_ofReal hFin).trans (le_iSup_of_le (τ l:ℝ)
      (le_iSup_of_le ⟨(τ l).2,le_rfl⟩ le_rfl))
  rw [Real.dist_eq]
  exact (ENNReal.ofReal_lt_ofReal_iff hε).1 (hStep.trans_lt hj)
