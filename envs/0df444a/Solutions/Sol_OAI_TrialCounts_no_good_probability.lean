-- Prove2me | solution 1 for OAI.TrialCounts.no_good_probability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:40:07.57258+00:00
-- url     : https://prove2.me/submissions/17a222e7-adce-4c54-926d-37d35732f903

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
theorem pl_var (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
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

theorem pl_count_memLp (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) : MemLp (count A) 2 μ := by
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
  exact MemLp.of_bound hmeas.aestronglyMeasurable _ (Filter.Eventually.of_forall hbd)

theorem pl_count_integral (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    μ[count A] = ∑ i, μ.real (A i) := by
  unfold count
  rw [integral_finsetSum _ (fun i _ => (integrable_const (1 : ℝ)).indicator (hA i))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show (fun _ : Ω => (1:ℝ)) = 1 from rfl, integral_indicator_one (hA i)]

omit [MeasurableSpace Ω] in
theorem pl_count_nonneg (A : I → Set Ω) (ω : Ω) : 0 ≤ count A ω := by
  unfold count
  exact Finset.sum_nonneg (fun i _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem solution (A B : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    {c γ τ : ℝ} (hcpos : 0 < Fintype.card I*c) (hτ : 0 < τ)
    (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c)
    (hbad : ∀ i, μ.real (B i) ≤ c*γ/τ) :
    μ.real {ω | ∀ i, ω ∈ A i → ω ∈ B i} ≤ 4/(Fintype.card I*c)+2*γ/τ := by
  set m : ℝ := Fintype.card I * c with hm
  have hsub : {ω | ∀ i, ω ∈ A i → ω ∈ B i} ⊆
      {ω | m/2 ≤ |count A ω - μ[count A]|} ∪ {ω | m/2 ≤ count B ω} := by
    intro ω hω
    have hmean : μ[count A] = m := by
      rw [pl_count_integral μ A hA]; simp [hc, hm]
    by_cases hN : count A ω ≤ m/2
    · left
      show m/2 ≤ |count A ω - μ[count A]|
      rw [hmean, abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    · right
      show m/2 ≤ count B ω
      have : count A ω ≤ count B ω := by
        unfold count
        apply Finset.sum_le_sum
        intro i _
        by_cases h : ω ∈ A i
        · simp [h, hω i h]
        · simp only [Set.indicator_of_notMem h]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      linarith
  have h1 : μ.real {ω | m/2 ≤ |count A ω - μ[count A]|} ≤ 4/m := by
    have hch := meas_ge_le_variance_div_sq (pl_count_memLp μ A hA) (by linarith : (0:ℝ) < m/2)
    have hv := pl_var μ A hA hc hpair
    have : variance (count A) μ / (m/2)^2 ≤ 4/m := by
      rw [div_le_div_iff₀ (by positivity) hcpos]
      have hv0 : 0 ≤ variance (count A) μ := variance_nonneg _ _
      nlinarith
    exact (ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)) hch).trans this
  have h2 : μ.real {ω | m/2 ≤ count B ω} ≤ 2*γ/τ := by
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ) (Filter.Eventually.of_forall (pl_count_nonneg B))
      ((pl_count_memLp μ B hB).integrable (by norm_num)) (m/2)
    have hEB : μ[count B] ≤ m * (γ/τ) := by
      rw [pl_count_integral μ B hB]
      calc ∑ i, μ.real (B i) ≤ ∑ _i : I, c*γ/τ := Finset.sum_le_sum (fun i _ => hbad i)
        _ = m * (γ/τ) := by simp [hm]; ring
    have : m/2 * μ.real {ω | m/2 ≤ count B ω} ≤ m/2 * (2*γ/τ) := by
      calc _ ≤ _ := hmk
        _ ≤ m * (γ/τ) := hEB
        _ = m/2 * (2*γ/τ) := by ring
    exact le_of_mul_le_mul_left this (by linarith)
  calc μ.real {ω | ∀ i, ω ∈ A i → ω ∈ B i}
      ≤ μ.real ({ω | m/2 ≤ |count A ω - μ[count A]|} ∪ {ω | m/2 ≤ count B ω}) := measureReal_mono hsub
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 4/m + 2*γ/τ := add_le_add h1 h2

