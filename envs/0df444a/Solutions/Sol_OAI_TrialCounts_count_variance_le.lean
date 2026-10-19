-- Prove2me | solution 1 for OAI.TrialCounts.count_variance_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:10:28.187697+00:00
-- url     : https://prove2.me/submissions/4e3f573c-447e-4f8e-ab6e-031836ce86f3

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts

open OAI OAI.TrialCounts
universe uI uOmega
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
variable {Ω : Type uOmega} {I : Type uI} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]


theorem solution (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c) :
    variance (count A) μ ≤ Fintype.card I*c := by
  classical
  have hind : ∀ i, Integrable ((A i).indicator (fun _ => (1 : ℝ))) μ :=
    fun i => (integrable_const (1 : ℝ)).indicator (hA i)
  have hmeas : Measurable (count A) := by
    unfold count
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hA i))
  have hbd : ∀ ω, ‖count A ω‖ ≤ Fintype.card I := by
    intro ω
    unfold count
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ i ∈ (Finset.univ : Finset I), |(A i).indicator (fun _ => (1 : ℝ)) ω| ≤ 1 := by
      intro i _
      by_cases h : ω ∈ A i <;> simp [h]
    calc ∑ i, |(A i).indicator (fun _ => (1 : ℝ)) ω| ≤ ∑ _i : I, (1 : ℝ) := Finset.sum_le_sum this
      _ = Fintype.card I := by simp
  have hL2 : MemLp (count A) 2 μ :=
    MemLp.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbd)
  rw [variance_eq_sub hL2]
  have hmean : μ[count A] = Fintype.card I * c := by
    unfold count
    rw [integral_finsetSum _ (fun i _ => hind i)]
    rw [Finset.sum_congr rfl (fun i _ => by
      rw [show (fun _ : Ω => (1:ℝ)) = 1 from rfl, integral_indicator_one (hA i), hc i])]
    simp
  have hsq : count A ^ 2 = fun ω => ∑ i, ∑ j, (A i ∩ A j).indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp only [Pi.pow_apply, count, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hi : ω ∈ A i <;> by_cases hj : ω ∈ A j <;> simp [hi, hj]
  have hsqint : μ[count A ^ 2] = ∑ i, ∑ j, μ.real (A i ∩ A j) := by
    rw [hsq, integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (integrable_const (1 : ℝ)).indicator ((hA i).inter (hA j))))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finsetSum _ (fun j _ => (integrable_const (1 : ℝ)).indicator ((hA i).inter (hA j)))]
    exact Finset.sum_congr rfl (fun j _ => by
      rw [show (fun _ : Ω => (1:ℝ)) = 1 from rfl, integral_indicator_one ((hA i).inter (hA j))])
  have hbound : ∀ i j, μ.real (A i ∩ A j) ≤ c*c + (if i = j then c - c*c else 0) := by
    intro i j
    by_cases h : i = j
    · subst h; simp [hc]
    · simp [h, hpair i j h]
  have hsum : ∑ i, ∑ j, μ.real (A i ∩ A j) ≤
      ∑ i : I, ∑ j : I, (c*c + (if i = j then c - c*c else 0)) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hbound i j))
  have hcalc : ∑ i : I, ∑ j : I, (c*c + (if i = j then c - c*c else 0)) =
      (Fintype.card I : ℝ)^2 * (c*c) + Fintype.card I * (c - c*c) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Finset.sum_ite_eq,
      Finset.mem_univ, if_true, nsmul_eq_mul]
    ring
  rw [hsqint, hmean]
  have hc2 : 0 ≤ c * c := mul_self_nonneg c
  have hn : (0 : ℝ) ≤ Fintype.card I := by positivity
  nlinarith [mul_nonneg hn hc2]

