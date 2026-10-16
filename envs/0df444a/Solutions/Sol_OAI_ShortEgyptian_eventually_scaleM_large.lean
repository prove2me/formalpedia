-- Prove2me | solution 1 for OAI.ShortEgyptian.eventually_scaleM_large
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:19:42.736164+00:00
-- url     : https://prove2.me/submissions/ca3634f2-bfc0-4928-9c00-821bbad632af

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/ScaleBounds.lean:L12-L25
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.eventually_scaleM_large. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ScaleBounds
import Theorems.Thm_OAI_ShortEgyptian_eventually_log_pow_le

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleGeometry ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset Classical Filter Topology

lemma scaleM_bounds (S : ℝ) (hlog : 1 ≤ Real.log S) (hS : 4*Real.log S ≤ S) :
    S/(2*Real.log S) ≤ (scaleM S:ℝ) ∧ (scaleM S:ℝ) ≤ S/Real.log S ∧
      (scaleM S:ℝ) ≤ S := by
  have hl : 0 < Real.log S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hf := Nat.sub_one_lt_floor (S/Real.log S)
  have hu := Nat.floor_le (div_nonneg hS0 hl.le)
  have hx : 4 ≤ S/Real.log S := (le_div_iff₀ hl).mpr (by linarith)
  refine ⟨?_,hu,hu.trans (div_le_self hS0 hlog)⟩
  dsimp [scaleM]
  have heq : S/(2*Real.log S) = (S/Real.log S)/2 := by ring
  rw [heq]
  linarith

end ShortEgyptian

end OAI

-- ---- from OAI.NumberTheory.ShortEgyptian.ScaleBounds ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open Filter Topology

lemma eventually_scaleM_large (A : ℝ) :
    ∀ᶠ S : ℝ in atTop, A*Real.log S ≤ (scaleM S:ℝ) := by
  filter_upwards [eventually_log_pow_le (2*(max A 0+2)) 2 (by norm_num : (0:ℝ)<1),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with S h hL
  rw [Real.rpow_one] at h
  have hA : 0 ≤ max A 0 := le_max_right _ _
  have hAA : A ≤ max A 0 := le_max_left _ _
  have hL0 : 0 < Real.log S := by linarith
  have hbig : 4*Real.log S ≤ S := by nlinarith [sq_nonneg (Real.log S),mul_nonneg hA (sq_nonneg (1+Real.log S))]
  have hm := (scaleM_bounds S hL hbig).1
  apply le_trans _ hm
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*Real.log S)).mpr
  have hh : 2*(max A 0)*(Real.log S)^2 ≤ S := by nlinarith [mul_nonneg hA hL0.le]
  nlinarith [mul_le_mul_of_nonneg_right hAA (sq_nonneg (Real.log S))]

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open Filter Topology


theorem solution : type_of% @_root_.OAI.ShortEgyptian.eventually_scaleM_large := @_root_.OAI.ShortEgyptian.eventually_scaleM_large
