-- Prove2me | solution 2 for OAI.TrialCounts.no_good_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:45:53.833612+00:00
-- url     : https://prove2.me/submissions/a13e1f76-1f54-45f0-a3e2-02af43e0ddf4

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/TrialCounts.lean:L154-L188
-- (upload_full_project.md Phase 4): solution for node OAI.TrialCounts.no_good_probability. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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
import Theorems.Thm_OAI_TrialCounts_count_variance_le

-- ---- from OAI.Probability.CriticalZ3.TrialCounts ----
namespace OAI

universe uI uOmega

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ShellEstimates
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem success_count_bound (S : Ω → ℝ) (hS : MemLp S 2 μ)
    {a : ℝ} (ha : 0 < a) (hmean : ∫ ω, S ω ∂μ = a)
    (hvar : variance S μ ≤ a) :
    μ.real {ω | S ω < a/2} ≤ 4/a := by
  have hcheb := meas_ge_le_variance_div_sq hS (show 0 < a/2 by positivity)
  rw [hmean] at hcheb
  have hs : {ω | S ω < a/2} ⊆ {ω | a/2 ≤ |S ω-a|} := by
    intro ω hω
    have hh : a/2 ≤ a-S ω := by dsimp at hω ⊢; linarith
    exact hh.trans (le_abs_self _ |>.trans_eq (abs_sub_comm a (S ω)))
  have hle : μ {ω | S ω < a/2} ≤ ENNReal.ofReal (variance S μ/(a/2)^2) :=
    (measure_mono hs).trans hcheb
  have hv0 : 0 ≤ variance S μ/(a/2)^2 := div_nonneg (variance_nonneg _ _) (sq_nonneg _)
  have hr : μ.real {ω | S ω < a/2} ≤ variance S μ/(a/2)^2 := by
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hle |>.trans_eq
      (ENNReal.toReal_ofReal hv0)
  apply hr.trans
  apply (div_le_iff₀ (sq_pos_of_pos (show 0 < a/2 by positivity))).mpr
  have he : (4/a)*(a/2)^2 = a := by field_simp; ring
  rwa [he]

/- Bad successes only need a first moment; no mutual independence is used. -/
omit [IsProbabilityMeasure μ] in
theorem bad_count_bound (Z : Ω → ℝ) (hZ : Integrable Z μ) (hZ0 : ∀ ω, 0 ≤ Z ω)
    {a γ τ : ℝ} (ha : 0 < a) (_hτ : 0 < τ)
    (hmean : ∫ ω, Z ω ∂μ ≤ a*γ/τ) :
    μ.real {ω | a/2 ≤ Z ω} ≤ 2*γ/τ := by
  have h := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hZ0) hZ (a/2)
  have hm : (a/2)*μ.real {ω | a/2 ≤ Z ω} ≤ a*γ/τ := h.trans hmean
  have he : (a/2)*(2*γ/τ) = a*γ/τ := by ring
  rw [←he] at hm
  exact (mul_le_mul_iff_right₀ (show 0 < a/2 by positivity)).mp hm

/- If there is no good success, either successes fall below half their mean
or at least half their mean are bad. This is purely deterministic. -/
end ShellEstimates

namespace TrialCounts
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {Ω : Type uOmega} {I : Type uI} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem count_memLp (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    MemLp (count A) 2 μ := by
  apply memLp_finsetSum
  intro i _
  exact (memLp_const (1 : ℝ)).indicator (hA i)

omit [MeasurableSpace Ω] in
theorem count_nonneg (A : I → Set Ω) (ω : Ω) : 0 ≤ count A ω := by
  apply Finset.sum_nonneg
  intro i _
  by_cases h : ω ∈ A i <;> simp [Set.indicator,h]

theorem count_mean (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i)) :
    (∫ ω, count A ω ∂μ) = ∑ i, μ.real (A i) := by
  unfold count
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    exact integral_indicator_one (hA i)
  · intro i _
    exact ((memLp_const (1 : ℝ)).indicator (hA i)).integrable (by norm_num : (1 : ENNReal) ≤ 2)

/-- No independence is required among bad successes or their quality tests. -/
theorem no_good_probability (A B : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    {c γ τ : ℝ} (hcpos : 0 < Fintype.card I*c) (hτ : 0 < τ)
    (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c)
    (hbad : ∀ i, μ.real (B i) ≤ c*γ/τ) :
    μ.real {ω | ∀ i, ω ∈ A i → ω ∈ B i} ≤ 4/(Fintype.card I*c)+2*γ/τ := by
  let a : ℝ := Fintype.card I*c
  have hm : (∫ ω, count A ω ∂μ) = a := by
    rw [count_mean μ A hA]
    simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,a]
  have hs := ShellEstimates.success_count_bound μ (count A) (count_memLp μ A hA)
    hcpos hm (count_variance_le μ A hA hc hpair)
  have hbmean : (∫ ω, count B ω ∂μ) ≤ a*γ/τ := by
    rw [count_mean μ B hB]
    calc
      _ ≤ ∑ _i : I, c*γ/τ := Finset.sum_le_sum (fun i _ => hbad i)
      _ = a*γ/τ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,a]; ring
  have hb := ShellEstimates.bad_count_bound μ (count B)
    ((count_memLp μ B hB).integrable (by norm_num)) (count_nonneg B) hcpos hτ hbmean
  have hsub : {ω | ∀ i, ω ∈ A i → ω ∈ B i} ⊆
      {ω | count A ω < a/2} ∪ {ω | a/2 ≤ count B ω} := by
    intro ω hω
    by_cases hs : count A ω < a/2
    · exact Or.inl hs
    · apply Or.inr
      apply (le_of_not_gt hs).trans
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : ω ∈ A i
      · simp [Set.indicator,hi,hω i hi]
      · simp only [Set.indicator,hi,ite_false]
        split_ifs <;> norm_num
  exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hs hb))

end TrialCounts

end OAI

-- ---- platform node ----
open OAI OAI.TrialCounts
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical


theorem solution.{uI,uOmega} : type_of% @_root_.OAI.TrialCounts.no_good_probability.{uI,uOmega} := @_root_.OAI.TrialCounts.no_good_probability.{uI,uOmega}
