-- Prove2me | solution 2 for OAI.TrialCounts.count_variance_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:44:17.680493+00:00
-- url     : https://prove2.me/submissions/2a8bdff3-c108-4261-afec-8502be3247b4

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/TrialCounts.lean:L125-L152
-- (upload_full_project.md Phase 4): solution for node OAI.TrialCounts.count_variance_le. The node keeps its source
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

/- Bad successes only need a first moment; no mutual independence is used. -/
/- If there is no good success, either successes fall below half their mean
or at least half their mean are bad. This is purely deterministic. -/
end ShellEstimates

namespace TrialCounts
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {Ω : Type uOmega} {I : Type uI} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem indicator_mean (A : Set Ω) (hA : MeasurableSet A) :
    (∫ ω, A.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real A :=
  integral_indicator_one hA

omit [MeasurableSpace Ω] in
theorem indicator_product (A B : Set Ω) :
    A.indicator (fun _ => (1 : ℝ)) * B.indicator (fun _ => (1 : ℝ)) =
      (A ∩ B).indicator (fun _ => (1 : ℝ)) := by
  funext ω
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [Set.indicator,hA,hB]

/-- Pairwise independence is all that the success-count step needs. -/
theorem count_variance_le (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c) :
    variance (count A) μ ≤ Fintype.card I*c := by
  let X (i : I) : Ω → ℝ := (A i).indicator (fun _ => (1 : ℝ))
  have hX (i : I) : MemLp (X i) 2 μ := (memLp_const (1 : ℝ)).indicator (hA i)
  have hcov (i j : I) : covariance (X i) (X j) μ ≤ if i = j then c else 0 := by
    have hprod : X i * X j = (A i ∩ A j).indicator (fun _ => (1 : ℝ)) :=
      indicator_product (A i) (A j)
    rw [covariance_eq_sub (hX i) (hX j),hprod,
      indicator_mean μ _ ((hA i).inter (hA j))]
    change μ.real (A i ∩ A j) -
      (∫ ω, (A i).indicator (fun _ => (1 : ℝ)) ω ∂μ)*
      (∫ ω, (A j).indicator (fun _ => (1 : ℝ)) ω ∂μ) ≤ _
    rw [indicator_mean μ _ (hA i),indicator_mean μ _ (hA j),hc i,hc j]
    by_cases hij : i = j
    · subst j
      simp only [ite_true,Set.inter_self,hc]
      nlinarith [sq_nonneg c]
    · simp only [hij,ite_false]
      linarith [hpair i j hij]
  have he : count A = ∑ i, X i := by ext ω; simp [count,X]
  rw [he,variance_sum hX]
  calc
    _ ≤ ∑ i : I, ∑ j : I, if i = j then c else 0 :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hcov i j))
    _ = Fintype.card I*c := by simp

end TrialCounts

end OAI

-- ---- platform node ----
open OAI OAI.TrialCounts
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical


theorem solution.{uI,uOmega} : type_of% @_root_.OAI.TrialCounts.count_variance_le.{uI,uOmega} := @_root_.OAI.TrialCounts.count_variance_le.{uI,uOmega}
