-- Prove2me | solution 1 for OAI.ShortEgyptian.depth_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:18:02.09987+00:00
-- url     : https://prove2.me/submissions/52ed7256-31cd-4c4d-a9f7-c5bffcc916eb

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ScaleGeometry.lean:L81-L95
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.depth_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_LevelSelection
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListConstruction
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleGeometry

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma depth_bound (S : ℝ) (hS : 0 < S) (hlog : 1 ≤ Real.log S)
    (hm : S/(2*Real.log S) ≤ (scaleM S:ℝ)) (hmS : (scaleM S:ℝ) ≤ S) :
    (depth S:ℝ) ≤ (3*(dimX:ℝ)*10000)*Real.log S := by
  have hl : 0 < Real.log S := by linarith
  have hm0 : 0 < (scaleM S:ℝ) := (div_pos hS (by positivity)).trans_le hm
  have hD : (2:ℝ) ≤ dimX := by norm_num [dimX,dimM]
  have hnum : 0 ≤ (dimX:ℝ)*S-scaleM S := by nlinarith
  have hh := Nat.ceil_lt_add_one (div_nonneg hnum (by positivity : (0:ℝ)≤(1/10000:ℝ)*scaleM S))
  have hSm := (div_le_iff₀ (by positivity : (0:ℝ)<2*Real.log S)).mp hm
  have hdiv : ((dimX:ℝ)*S-scaleM S)/((1/10000:ℝ)*scaleM S) ≤
      2*(dimX:ℝ)*10000*Real.log S := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hSm (by positivity : (0:ℝ)≤dimX)]
  change (⌈_⌉₊:ℝ) ≤ _
  nlinarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset Classical Filter Topology


theorem solution : type_of% @_root_.OAI.ShortEgyptian.depth_bound := @_root_.OAI.ShortEgyptian.depth_bound
