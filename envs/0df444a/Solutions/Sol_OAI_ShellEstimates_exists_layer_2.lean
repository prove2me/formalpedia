-- Prove2me | solution 2 for OAI.ShellEstimates.exists_layer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:41:13.326566+00:00
-- url     : https://prove2.me/submissions/223b19b3-d514-428f-b487-3de3f533b96b

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/TrialCounts.lean:L15-L35
-- (upload_full_project.md Phase 4): solution for node OAI.ShellEstimates.exists_layer. The node keeps its source
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

/-- Averaging disjoint blocking events supplies a deterministic shell layer. -/
theorem exists_layer {I : Type uI} [Fintype I] [Nonempty I]
    (Q A : I → Set Ω) (hAm : ∀ i, MeasurableSet (A i))
    (hAd : Pairwise (fun i j => Disjoint (A i) (A j))) {α : ℝ} (hα : 0 < α)
    (hblock : ∀ i, α*μ.real (Q i) ≤ μ.real (A i)) :
    ∃ i, μ.real (Q i) ≤ 1/(α*Fintype.card I) := by
  have hs : ∑ i, μ.real (A i) ≤ 1 := by
    rw [←measureReal_iUnion_fintype hAd hAm]
    exact measureReal_le_one
  have hsQ : α*(∑ i, μ.real (Q i)) ≤ 1 := by
    rw [Finset.mul_sum]
    exact (Finset.sum_le_sum (fun i _ => hblock i)).trans hs
  have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
  by_contra! hnone
  have ht : (∑ _i : I, 1/(α*Fintype.card I)) < ∑ i, μ.real (Q i) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => hnone i)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at ht
  have he : (Fintype.card I : ℝ)*(1/(α*Fintype.card I)) = 1/α := by field_simp
  rw [he] at ht
  have hh := (div_lt_iff₀ hα).mp ht
  nlinarith

/- Bad successes only need a first moment; no mutual independence is used. -/
/- If there is no good success, either successes fall below half their mean
or at least half their mean are bad. This is purely deterministic. -/
end ShellEstimates

namespace TrialCounts
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {Ω : Type uOmega} {I : Type uI} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

end TrialCounts

end OAI

-- ---- platform node ----
open OAI OAI.ShellEstimates
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical


theorem solution.{uI,uOmega} : type_of% @_root_.OAI.ShellEstimates.exists_layer.{uI,uOmega} := @_root_.OAI.ShellEstimates.exists_layer.{uI,uOmega}
