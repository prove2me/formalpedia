-- Prove2me | solution 1 for OAI.ShortEgyptian.log_one_sub_inverse_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:54:07.180779+00:00
-- url     : https://prove2.me/submissions/df5d9da7-fe95-499a-970c-35b923b836a6

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/RecurrenceUnrolling.lean:L52-L65
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.log_one_sub_inverse_lower. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ResidueSystem
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TerminalScale
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DescentSets
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_MomentRecurrence

-- ---- from OAI.NumberTheory.ShortEgyptian.RecurrenceUnrolling ----
namespace OAI

namespace ShortEgyptian

attribute [local instance] scaleFinDecidableEq

open scoped BigOperators
open Finset Classical

lemma log_one_sub_inverse_lower (r : ℝ) (hr : 2 ≤ r) :
    -(2/r) ≤ Real.log (1-1/r) := by
  have hrp : 0 < r := by linarith
  have hrm : 0 < r-1 := by linarith
  have ha : 0 < 1-1/r := by rw [sub_pos,div_lt_one hrp]; linarith
  have he : (1-1/r)⁻¹=r/(r-1) := by field_simp
  have hd : r/(r-1) ≤ 1+2/r := by
    apply (div_le_iff₀ hrm).mpr
    apply (mul_le_mul_iff_of_pos_right hrp).mp
    field_simp
    nlinarith
  have hl := Real.one_sub_inv_le_log_of_pos ha
  rw [he] at hl
  linarith

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
attribute [local instance] scaleFinDecidableEq
open scoped BigOperators
open Finset Classical


theorem solution : type_of% @_root_.OAI.ShortEgyptian.log_one_sub_inverse_lower := @_root_.OAI.ShortEgyptian.log_one_sub_inverse_lower
