-- Prove2me | solution 1 for OAI.ShortEgyptian.random_error_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:50:14.18789+00:00
-- url     : https://prove2.me/submissions/6f7bc632-d51e-4652-a79f-8975985317f9

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/RandomBounds.lean:L123-L140
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.random_error_sum. The node keeps its source
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

-- ---- from OAI.NumberTheory.ShortEgyptian.RandomBounds ----
namespace OAI

universe uJ uA

namespace ShortEgyptian

open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable

lemma random_error_sum (m V : ℝ) (hw : 100 ≤ min m V) :
    Real.exp (-m/16)+Real.exp (-(1/20:ℝ)*V)+Real.exp (-(1/5:ℝ)*V) ≤
      Real.exp (-(1/100:ℝ)*min m V) := by
  let w := min m V
  have hm : w ≤ m := min_le_left _ _
  have hV : w ≤ V := min_le_right _ _
  have hw0 : 0 ≤ w := by dsimp [w]; linarith
  have h1 : Real.exp (-m/16) ≤ Real.exp (-(1/20:ℝ)*w) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-(1/20:ℝ)*V) ≤ Real.exp (-(1/20:ℝ)*w) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-(1/5:ℝ)*V) ≤ Real.exp (-(1/20:ℝ)*w) := Real.exp_le_exp.mpr (by linarith)
  have h4 : (3:ℝ) ≤ Real.exp ((1/25:ℝ)*w) := by
    have hh := Real.add_one_le_exp ((1/25:ℝ)*w)
    dsimp [w] at *
    linarith
  calc
    _ ≤ 3*Real.exp (-(1/20:ℝ)*w) := by linarith
    _ ≤ Real.exp ((1/25:ℝ)*w)*Real.exp (-(1/20:ℝ)*w) := mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = _ := by rw [←Real.exp_add]; congr 1; dsimp [w]; ring
end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset
attribute [local instance] Classical.propDecidable


theorem solution : type_of% @_root_.OAI.ShortEgyptian.random_error_sum := @_root_.OAI.ShortEgyptian.random_error_sum
