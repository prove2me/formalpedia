-- Prove2me | solution 1 for OAI.InfiniteConditioning.map_replace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:06:43.901908+00:00
-- url     : https://prove2.me/submissions/aee4dc9b-57bb-45db-9b56-8598dcb4b5b4

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

open OAI OAI.InfiniteConditioning
universe uF
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]
theorem hc_map_replace {E : Type} (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    (ProductCylinder.law p).map (replace J ξ) = ProductCylinder.law (fixedParameter p J ξ) := by
  have hr : replace J ξ = fun ω e => (fun (b : Bool) => if e ∈ J then ξ e else b) (ω e) := by
    funext ω e; simp [replace]
  unfold ProductCylinder.law
  rw [hr, Measure.infinitePi_map_pi _ (fun e => Measurable.of_discrete)]
  congr 1; funext e
  by_cases he : e ∈ J
  · have h1 : (ite (e ∈ J) (ξ e) : Bool → Bool) = fun _ => ξ e := by funext b; simp [he]
    rw [h1, Measure.map_const, measure_univ, one_smul]
    unfold fixedParameter
    rw [if_pos he]
    cases ξ e
    · simp
    · simp
  · have h1 : (ite (e ∈ J) (ξ e) : Bool → Bool) = id := by funext b; simp [he]
    rw [h1, Measure.map_id]
    unfold fixedParameter
    rw [if_neg he]

omit [Countable E] in
theorem solution (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    (ProductCylinder.law p).map (replace J ξ) = ProductCylinder.law (fixedParameter p J ξ) := by
  exact hc_map_replace p J ξ

