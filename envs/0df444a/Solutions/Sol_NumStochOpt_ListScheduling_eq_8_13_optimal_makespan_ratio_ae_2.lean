-- Prove2me | solution 2 for NumStochOpt.ListScheduling.eq_8_13_optimal_makespan_ratio_ae
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:25.803065+00:00
-- url     : https://prove2.me/submissions/4523d9aa-cae5-4d93-a269-ad28b08a2391

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule
import Theorems.Thm_NumStochOpt_ListScheduling_eq_8_12_machines_times_max_ae
import Theorems.Thm_NumStochOpt_ListScheduling_eq_8_10_makespan_sandwich

-- carved verbatim out of submission 89a19df5-a925-46c4-b5d8-29085d2d9544, lines 288-329

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics NumStochOpt.ListScheduling in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n)
    (hmO : (fun n : ℕ => (m n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => optMakespan n (m n) (fun j => p j ω) / (n * μ / m n))
      atTop (𝓝 1) := by
  have hint : Integrable (p 0) P := by
    refine Integrable.mono' (hsq.add (integrable_const (1 : ℝ)))
      (hmeas 0).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    have h0 := hnonneg 0 ω
    rw [Real.norm_of_nonneg h0]
    show p 0 ω ≤ p 0 ω ^ 2 + 1
    nlinarith [sq_nonneg (p 0 ω - 1)]
  have hSL := ProbabilityTheory.strong_law_ae_real p hint
    (fun i j hij => hindep.indepFun hij) hident
  have hE := NumStochOpt.ListScheduling.eq_8_12_machines_times_max_ae p hmeas hindep hident hnonneg hsq μ hmean hμ m hm hmO
  filter_upwards [hSL, hE] with ω hω hTω
  rw [hmean] at hω
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, p i ω with hSdef
  have hL : Tendsto (fun n : ℕ => (S n - n * μ) / (n * μ) + 1) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (S n / n) / μ) atTop (𝓝 (μ / μ)) := hω.div_const μ
    rw [div_self hμ.ne'] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
    ring
  have hU : Tendsto (fun n : ℕ => (S n - n * μ) / (n * μ) + 1
      + (m n : ℝ) * maxProcTime n (fun j => p j ω) / (n * μ)) atTop (𝓝 1) := by
    have := hL.add hTω
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (NumStochOpt.ListScheduling.eq_8_10_makespan_sandwich n (m n) (fun j => p j ω) μ (fun j => hnonneg j ω) hn (hm n) hμ).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h := NumStochOpt.ListScheduling.eq_8_10_makespan_sandwich n (m n) (fun j => p j ω) μ (fun j => hnonneg j ω) hn (hm n) hμ
    exact h.2.1.trans h.2.2

end
