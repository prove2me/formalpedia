-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_small_time_dyadic_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:51:13.261299+00:00
-- url     : https://prove2.me/submissions/44dc43fe-5490-4416-870d-a619617006e9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch04_ito43_compact_kernel_bound
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_nnreal_tendsto
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_time_ge_nnreal
open MeasureTheory Filter ProbabilityTheory Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution {Ω : Type} [MeasurableSpace Ω]
    (X : NNReal → Ω → ℝ)
    (hX : Measurable (fun z : NNReal × Ω => X z.1 z.2))
    (hCad : ∀ w, IsCadlag (fun t => X t w)) (T : NNReal) :
    let d : ℕ → ℕ × ℕ → NNReal := fun n k =>
      min (T / (n : NNReal)) ((k.1 : NNReal) / 2 ^ k.2)
    let K : ℕ → (ℕ × ℕ) → Ω → ℝ := fun n k w => |X (d n k) w - X 0 w|
    let B : ℕ → Ω → ℝ := fun n w => ⨆ k, K n k w
    ∀ w, Tendsto (fun n => B n w) atTop (nhds 0) := by
  intro d K B
  have hbdd (n : ℕ) (w : Ω) : BddAbove (range (fun k => K n k w)) := by
    obtain ⟨C,_,hC⟩ := Kyprianou.Ch04.ito43_compact_kernel_bound
      (fun t => X t w) (hCad w) (fun z : ℝ × ℝ => z.2 - X 0 w)
      (by fun_prop) (T / (n : NNReal))
    exact ⟨C, by rintro _ ⟨k,rfl⟩; exact hC 0 ⟨le_rfl,by positivity⟩ _ (min_le_left _ _)⟩
  have hle (n : ℕ) (w : Ω) (k : ℕ × ℕ) : K n k w ≤ B n w :=
    le_ciSup (hbdd n w) k
  have hnon (n : ℕ) (w : Ω) : 0 ≤ B n w :=
    (abs_nonneg _).trans (hle n w (0,0))
  intro w
  have hc : ContinuousAt (fun t => X t w) 0 := by
    simpa only [Ici_zero_eq_univ, continuousWithinAt_univ] using (hCad w 0).1
  have ht : Tendsto (fun n : ℕ => T / (n : NNReal)) atTop (nhds 0) := by
    apply NNReal.tendsto_coe.mp
    simpa using tendsto_const_div_atTop_nhds_zero_nat (T : ℝ)
  apply Metric.tendsto_atTop.mpr
  intro e he
  obtain ⟨δ,hδ,hδb⟩ := Metric.continuousAt_iff.mp hc (e/2) (by positivity)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht δ hδ
  refine ⟨N,fun n hn => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hnon n w)]
  have hB : B n w ≤ e/2 := by
    apply ciSup_le
    intro k
    apply le_of_lt
    have hdist : dist (d n k) 0 < δ := by
      have H := hN n hn
      simp only [NNReal.dist_eq,NNReal.coe_zero,sub_zero,abs_of_nonneg (NNReal.coe_nonneg _)] at H ⊢
      have hd : d n k ≤ T / (n : NNReal) := min_le_left _ _
      exact lt_of_le_of_lt (by exact_mod_cast hd) H
    exact hδb hdist
  linarith
