-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_finite_horizon_balance
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:25:50.169522+00:00
-- url     : https://prove2.me/submissions/fbb17632-6d8d-40a7-b1ce-ca02c2b7baad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_subsequence_limit_paths
import Theorems.Thm_ManyServerQED_Scheduling_discounted_hjb_limit_expected_balance
import Theorems.Thm_ManyServerQED_Scheduling_discounted_polynomial_terminal_expectation_vanishes
import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k] (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
      IsWorkConserving n (X n) (Ψ n))
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    :
    ∀ s : ℕ → ℕ, Tendsto s atTop atTop →
      ∃ r : ℕ → ℕ, Tendsto r atTop atTop ∧ ∃ C F G : ℕ → ℝ,
        (∀ T, 0 ≤ C T ∧ 0 ≤ G T ∧ C T = f x - F T + G T) ∧
        Tendsto F atTop (𝓝 0) ∧
        (∀ T : ℕ, Tendsto (fun j =>
          ∫⁻ ω, ∫⁻ t in Set.Ioc (0:ℝ) (T:ℝ),
            ENNReal.ofReal (Real.exp (-γ*t) *
              costOfTilde Lt (M.Xhat (s (r j)) (X (s (r j))) ω t)
                (uProc (s (r j)) u0 (X (s (r j))) (Ψ (s (r j))) ω t)) ∂volume ∂M.P)
          atTop (𝓝 (ENNReal.ofReal (C T)))) ∧
        (UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) i *
            grad f (M.Xhat n (X n) ω s) i +
          costOfTilde Lt (M.Xhat n (X n) ω s) (uProc n u0 (X n) (Ψ n) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (X n) ω s)
            (grad f (M.Xhat n (X n) ω s)))])
      (fun _ => 0) → ∀ T, G T = 0) := by
  intro s hs
  obtain ⟨r, hr, d, hDist, hb, hsup, hzero⟩ :=
    queue_hjb_subsequence_limit_paths M Lt ϱ mL mU γ hA2 hA3 hγ u0 hu0
      X0 x hX0 X Ψ hpol f hf hHJB s hs
  let : IsProbabilityMeasure d.P := d.isProb
  let C (T : ℕ) := ∫ ω, d.cost T ω ∂d.P
  let F (T : ℕ) := ∫ ω, Real.exp (-γ*(T:ℝ)) * f (d.X T ω) ∂d.P
  let G (T : ℕ) := ∫ ω, d.gap T ω ∂d.P
  have hF := (discounted_polynomial_terminal_expectation_vanishes d.P d.X
    (fun t => (d.X_adapted t).mono (d.F.le t) le_rfl) d.X_moment f hf γ hγ).2
  refine ⟨r, hr, C, F, G, ?_, hF, hDist, ?_⟩
  · intro T
    have hC : 0 ≤ C T := by
      apply integral_nonneg_of_ae
      filter_upwards [d.cost_zero, d.cost_increases] with ω h0 hmon
      change (0:ℝ) ≤ d.cost (T:ℝ≥0) ω
      simpa only [h0] using hmon (show (0:ℝ≥0) ≤ T from zero_le)
    have hG : 0 ≤ G T := by
      apply integral_nonneg_of_ae
      filter_upwards [d.cost_zero, d.gap_eq, d.gap_increases] with ω h0 heq hmon
      have hZ : d.gap 0 ω = 0 := by simpa [h0] using heq 0
      change (0:ℝ) ≤ d.gap (T:ℝ≥0) ω
      simpa only [hZ] using hmon (show (0:ℝ≥0) ≤ T from zero_le)
    exact ⟨hC,hG,(discounted_hjb_limit_expected_balance M.diffData (costOfTilde Lt) ϱ mL γ
      hA2.cost hγ x f hf hHJB d hb hsup T).2⟩
  · intro h49 T
    apply integral_eq_zero_of_ae
    exact hzero h49 T
