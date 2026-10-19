-- Prove2me | solution 1 for OAI.BackwardIntertwiners.sum_coordinateDistance_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:08:36.384552+00:00
-- url     : https://prove2.me/submissions/c64f9e54-ada4-44c4-9a7c-1fb37bc983be

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/FiberMaps.lean:L32-L56
-- (upload_full_project.md Phase 4): solution for node OAI.BackwardIntertwiners.sum_coordinateDistance_lower. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps

-- ---- from OAI.Analysis.BackwardIntertwiners.FiberMaps ----
namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

lemma powerCost_add_two (n : ℕ) : powerCost (n+2) = powerCost n + n+2 := by
  unfold powerCost
  have he : (n+2+1)^2 = (n+1)^2 + 4*(n+2) := by ring
  rw [he]
  omega

lemma coordinateDistance_pos (j : ℤ) : 1 ≤ coordinateDistance j := by
  unfold coordinateDistance
  omega

lemma coordinateDistance_endpoints (j : ℤ) (n : ℕ) :
    (n:ℤ)+2 ≤ coordinateDistance j + coordinateDistance (j+(n:ℤ)+1) := by
  have h₁ : -j ≤ coordinateDistance j := le_max_right _ _
  have h₂ : j+(n:ℤ)+1+1 ≤ coordinateDistance (j+(n:ℤ)+1) := le_max_left _ _
  omega

lemma sum_coordinateDistance_lower (n : ℕ) (j : ℤ) :
    (powerCost n : ℤ) ≤ ∑ r ∈ Finset.range n, coordinateDistance (j+(r:ℤ)) := by
  induction n using Nat.twoStepInduction generalizing j with
  | zero => simp [powerCost]
  | one => simpa [powerCost] using coordinateDistance_pos j
  | more n ih _ =>
    have hsum : (∑ r ∈ Finset.range (n+2), coordinateDistance (j+(r:ℤ))) =
        coordinateDistance j + (∑ r ∈ Finset.range n, coordinateDistance ((j+1)+(r:ℤ))) +
        coordinateDistance (j+(n:ℤ)+1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      congr 1
      · rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        congr 1
        ring
      · congr 1
        ring
    rw [hsum, powerCost_add_two]
    have hmid := ih (j+1)
    have hend := coordinateDistance_endpoints j n
    push_cast
    omega

end
end BackwardIntertwiners

end OAI

-- ---- platform node ----
open OAI OAI.BackwardIntertwiners
open Filter
open scoped Topology
open Topology MeasureTheory Set
open scoped ENNReal


theorem solution : type_of% @_root_.OAI.BackwardIntertwiners.sum_coordinateDistance_lower := @_root_.OAI.BackwardIntertwiners.sum_coordinateDistance_lower
