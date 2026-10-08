-- Prove2me | solution 1 for MeasureTheory.Measure.eq_of_interval_average
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T00:30:52.72607+00:00
-- url     : https://prove2.me/submissions/ea6ddb03-75b6-4025-be58-8438ed723c4d

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum

open MeasureTheory Filter Set
open scoped Topology

namespace HerglotzStieltjes

noncomputable def intervalWeight (a b x : ℝ) : ℝ :=
  ((Ioo a b).indicator (fun _ => (1 : ℝ)) x +
    (Icc a b).indicator (fun _ => (1 : ℝ)) x) / 2
theorem intervalWeight_integrable (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    Integrable (intervalWeight a b) μ :=
  ((integrable_const 1).indicator measurableSet_Ioo |>.add
    ((integrable_const 1).indicator measurableSet_Icc)).div_const 2

theorem integral_intervalWeight (μ : Measure ℝ) [IsFiniteMeasure μ] (a b : ℝ) :
    (∫ x, intervalWeight a b x ∂μ) =
      ((μ (Ioo a b)).toReal + (μ (Icc a b)).toReal) / 2 := by
  unfold intervalWeight
  rw [integral_div, integral_add]
  · simp [integral_indicator measurableSet_Ioo, integral_indicator measurableSet_Icc, measureReal_def]
  · exact (integrable_const 1).indicator measurableSet_Ioo
  · exact (integrable_const 1).indicator measurableSet_Icc

theorem intervalWeight_norm_le (a b x : ℝ) : ‖intervalWeight a b x‖ ≤ 1 := by
  unfold intervalWeight
  simp only [indicator_apply]
  split_ifs <;> norm_num

theorem expanded_intervalWeight_tendsto (a b x : ℝ) :
    Tendsto (fun δ : ℝ => intervalWeight (a-δ) (b+δ) x) (𝓝[>] 0)
      (𝓝 ((Icc a b).indicator (fun _ => (1 : ℝ)) x)) := by
  by_cases hx : x ∈ Icc a b
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0 < δ at hδ
    have h₁ : x ∈ Ioo (a-δ) (b+δ) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h₂ : x ∈ Icc (a-δ) (b+δ) := ⟨h₁.1.le,h₁.2.le⟩
    simp [intervalWeight, hx, h₁, h₂]
  · simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < a-x :=
        (eventually_lt_nhds (sub_pos.mpr hx)).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with δ hδ
      have h₁ : x ∉ Ioo (a-δ) (b+δ) := fun h => by linarith [h.1]
      have h₂ : x ∉ Icc (a-δ) (b+δ) := fun h => by linarith [h.1]
      have h₃ : x ∉ Icc a b := fun h => by linarith [h.1]
      simp [intervalWeight,h₁,h₂,h₃]
    · have he : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < x-b :=
        (eventually_lt_nhds (sub_pos.mpr hx)).filter_mono nhdsWithin_le_nhds
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with δ hδ
      have h₁ : x ∉ Ioo (a-δ) (b+δ) := fun h => by linarith [h.2]
      have h₂ : x ∉ Icc (a-δ) (b+δ) := fun h => by linarith [h.2]
      have h₃ : x ∉ Icc a b := fun h => by linarith [h.2]
      simp [intervalWeight,h₁,h₂,h₃]

theorem integral_expanded_intervalWeight_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) :
    Tendsto (fun δ : ℝ => ∫ x, intervalWeight (a-δ) (b+δ) x ∂μ)
      (𝓝[>] 0) (𝓝 ((μ (Icc a b)).toReal)) := by
  have h := tendsto_integral_filter_of_dominated_convergence (μ := μ)
    (F := fun δ x => intervalWeight (a-δ) (b+δ) x)
    (f := (Icc a b).indicator (fun _ => (1 : ℝ))) (fun _ => (1 : ℝ))
    (Eventually.of_forall fun δ => (intervalWeight_integrable μ (a-δ) (b+δ)).aestronglyMeasurable)
    (Eventually.of_forall fun δ => Eventually.of_forall fun x => intervalWeight_norm_le _ _ x)
    (integrable_const 1) (Eventually.of_forall fun x => expanded_intervalWeight_tendsto a b x)
  simpa [integral_indicator measurableSet_Icc, measureReal_def] using h

end HerglotzStieltjes

open HerglotzStieltjes

theorem solution (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ a b : ℝ, a < b →
      ((μ (Ioo a b)).toReal + (μ (Icc a b)).toReal) / 2 =
      ((ν (Ioo a b)).toReal + (ν (Icc a b)).toReal) / 2) : μ = ν := by
  apply Measure.ext_of_Icc
  intro a b hab
  have he : (fun δ : ℝ => ∫ x, intervalWeight (a-δ) (b+δ) x ∂μ) =ᶠ[𝓝[>] 0]
      (fun δ : ℝ => ∫ x, intervalWeight (a-δ) (b+δ) x ∂ν) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    change 0 < δ at hδ
    rw [integral_intervalWeight, integral_intervalWeight]
    exact h _ _ (by linarith)
  have hr := tendsto_nhds_unique (integral_expanded_intervalWeight_tendsto μ a b)
    ((integral_expanded_intervalWeight_tendsto ν a b).congr' he.symm)
  exact ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ν _) |>.mp hr

