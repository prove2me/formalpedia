-- Prove2me | solution 2 for OAI.EntropyRateDimension.FiniteEntropy.binEntropy_bits_le_three_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T05:32:59.675653+00:00
-- url     : https://prove2.me/submissions/e0c32869-021e-46bb-b5a9-a11a13b406a5

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/SelfSimilar/FiniteEntropy.lean:L518-L533
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyRateDimension.FiniteEntropy.binEntropy_bits_le_three_sqrt. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SelfSimilar
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_Basic
import Definitions.Def_OAI_MeasureTheory_SelfSimilar_FiniteEntropy

-- ---- from OAI.MeasureTheory.SelfSimilar.FiniteEntropy ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uι uα uβ uγ uδ

section
open scoped BigOperators ENNReal
open MeasureTheory
namespace EntropyRateDimension
namespace FiniteEntropy

theorem binEntropy_bits_le_three_sqrt {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.binEntropy q / Real.log 2 ≤ 3 * Real.sqrt q := by
  have hs : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
  have hs2 : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
  have h1 := Real.negMulLog_le_one_sub_self hs
  have h2 := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr hq1)
  have hmul := mul_le_mul_of_nonneg_left h1 hs
  have hident := Real.negMulLog_mul (Real.sqrt q) (Real.sqrt q)
  rw [hs2] at hident
  have hbound : Real.binEntropy q ≤ 2 * Real.sqrt q := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    nlinarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hlog).mpr
  have hlog2 : (2 : ℝ) ≤ 3 * Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hlog2)]

end FiniteEntropy
end EntropyRateDimension
end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyRateDimension OAI.EntropyRateDimension.FiniteEntropy
open scoped BigOperators ENNReal
open MeasureTheory


theorem solution : type_of% @_root_.OAI.EntropyRateDimension.FiniteEntropy.binEntropy_bits_le_three_sqrt := @_root_.OAI.EntropyRateDimension.FiniteEntropy.binEntropy_bits_le_three_sqrt
