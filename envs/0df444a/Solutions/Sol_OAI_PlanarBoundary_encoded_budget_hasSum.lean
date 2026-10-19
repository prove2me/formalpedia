-- Prove2me | solution 1 for OAI.PlanarBoundary.encoded_budget_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:19:52.473362+00:00
-- url     : https://prove2.me/submissions/44bd3dbd-742c-447d-b523-bbc326ea0eec

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

open OAI OAI.PlanarBoundary
universe uOmega
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Filter Topology
open Classical _root_.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]


theorem solution :
    HasSum (fun n : ℕ => 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7)) (25/144 : ℝ) := by
  have hterm : ∀ n : ℕ, 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7) = 4 * ((n:ℝ) * (1/25 : ℝ)^n) := by
    intro n
    have h2 : 2*CriticalScales.contourError = (1/100 : ℝ)^7 := by
      norm_num [CriticalScales.contourError]
    rw [h2, ← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 1/100)]
    have : ((7:ℕ):ℝ) * ((n:ℝ)/7) = (n:ℕ) := by push_cast; ring
    rw [this, Real.rpow_natCast]
    rw [mul_assoc, mul_assoc, ← mul_pow]
    norm_num
  simp_rw [hterm]
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) (r := 1/25) (by norm_num)).mul_left 4
  have e : (25/144:ℝ) = 4 * (1 / 25 / (1 - 1 / 25) ^ 2) := by norm_num
  rw [e]
  exact h

