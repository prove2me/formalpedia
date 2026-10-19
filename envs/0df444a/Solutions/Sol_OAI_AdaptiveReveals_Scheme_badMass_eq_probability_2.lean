-- Prove2me | solution 2 for OAI.AdaptiveReveals.Scheme.badMass_eq_probability
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:46:17.477026+00:00
-- url     : https://prove2.me/submissions/26fed06c-e9bc-432b-bf81-98b67186e115

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/AdaptiveReveals.lean:L141-L155
-- (upload_full_project.md Phase 4): solution for node OAI.AdaptiveReveals.Scheme.badMass_eq_probability. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Theorems.Thm_OAI_InfiniteConditioning_measure_select

-- ---- from OAI.Probability.CriticalZ3.AdaptiveReveals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uF

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace AdaptiveReveals
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]

namespace Scheme
variable (P : Scheme E V S)

omit [DecidableEq V] in
theorem badMass_eq_probability (s : S) : P.badMass s =
    (ProductCylinder.law (P.parameter s)).real
      {ω | P.bad s ((P.reveal s).restrict ω) = true} := by
  have h := measure_select (P.parameter s) (P.reveal s)
    (fun a => if P.bad s a = true then Set.univ else ∅)
    (fun a => by split_ifs <;> simp)
  have heq : {ω : E → Bool | ω ∈ if P.bad s ((P.reveal s).restrict ω) = true then Set.univ else ∅} =
      {ω | P.bad s ((P.reveal s).restrict ω) = true} := by aesop
  rw [heq] at h
  rw [h]
  unfold badMass
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : P.bad s a = true <;> simp [weight,ha,probReal_univ]

end Scheme
end AdaptiveReveals

namespace InfiniteConditioning
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

namespace History
end History
end InfiniteConditioning

end OAI

-- ---- platform node ----
open OAI OAI.AdaptiveReveals OAI.AdaptiveReveals.Scheme
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning


theorem solution : type_of% @_root_.OAI.AdaptiveReveals.Scheme.badMass_eq_probability := @_root_.OAI.AdaptiveReveals.Scheme.badMass_eq_probability
