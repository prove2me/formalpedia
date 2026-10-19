-- Prove2me | solution 2 for OAI.PlanarBoundary.encoded_budget_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:33:02.622707+00:00
-- url     : https://prove2.me/submissions/5baf3c9c-28da-438e-9506-2a781c0c5090

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Peierls.lean:L96-L109
-- (upload_full_project.md Phase 4): solution for node OAI.PlanarBoundary.encoded_budget_hasSum. The node keeps its source
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

-- ---- from OAI.Probability.CriticalZ3.Scales ----
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open Filter Topology
namespace CriticalScales

theorem contour_power (n : ℕ) :
    (2*contourError)^((n : ℝ)/7) = (1/100 : ℝ)^n := by
  have he : 2*contourError = (1/100 : ℝ)^7 := by unfold contourError; ring
  rw [he,←Real.rpow_natCast,←Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1/100)]
  have hn : (7 : ℝ)*((n : ℝ)/7) = n := by ring
  norm_num only [Nat.cast_ofNat]
  rw [hn,Real.rpow_natCast]

end CriticalScales

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Model
end Model

namespace ScaleData
variable {model : Model} (s : ScaleData model)

end ScaleData
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Peierls ----
namespace OAI

universe uOmega

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Filter Topology

namespace PlanarBoundary
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Exact numerical budget for the benign overcount of encoded trails. -/
theorem encoded_budget_hasSum :
    HasSum (fun n : ℕ => 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7)) (25/144 : ℝ) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(4/100 : ℝ)‖ < 1)).mul_left 4
  have he (n : ℕ) : 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7) =
      4*((n : ℝ)*(4/100 : ℝ)^n) := by
    rw [CriticalScales.contour_power]
    have hp : (4/100 : ℝ)^n = 4^n*(1/100 : ℝ)^n := by rw [←mul_pow]; congr 1; ring
    rw [hp]
    ring
  simp_rw [he]
  have hz : 4*((4/100 : ℝ)/(1-4/100)^2) = 25/144 := by norm_num
  rw [hz] at h
  exact h

end PlanarBoundary

end OAI

-- ---- platform node ----
open OAI OAI.PlanarBoundary
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Filter Topology
open Classical _root_.MeasureTheory ProbabilityTheory


theorem solution : type_of% @_root_.OAI.PlanarBoundary.encoded_budget_hasSum := @_root_.OAI.PlanarBoundary.encoded_budget_hasSum
