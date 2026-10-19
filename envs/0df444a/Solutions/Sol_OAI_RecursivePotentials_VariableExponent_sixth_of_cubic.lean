-- Prove2me | solution 1 for OAI.RecursivePotentials.VariableExponent.sixth_of_cubic
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:12:54.998638+00:00
-- url     : https://prove2.me/submissions/3c6a6fc2-c6f2-41ec-8268-6df8c6138b8f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/VariableCompletion.lean:L443-L482
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.VariableExponent.sixth_of_cubic. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RecursivePotentials
import Definitions.Def_OAI_Analysis_RecursivePotentials_Model
import Definitions.Def_OAI_Analysis_RecursivePotentials_TreeGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_ZeroRootGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_EquivalentNorms
import Definitions.Def_OAI_Analysis_RecursivePotentials_JoinedGeometry
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableEstimates
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableCompletion

-- ---- from OAI.Analysis.RecursivePotentials.VariableCompletion ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

namespace VariableTree

open FiniteRootedTree

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end VariableTree

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationSpace

namespace AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationVector

namespace AggregationSpace

open UniformSpace

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationSpace

namespace VariableExponent

lemma sixthConstant_le_twice_cubic : sixthConstant ≤ 2 * cubicConstant := by
  have he : Real.exp (-(Real.exp 1 - 1)) ≤ (1/2:ℝ) := by
    calc
      _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith [Real.exp_one_gt_two])
      _ = (Real.exp 1)⁻¹ := Real.exp_neg 1
      _ ≤ (1/2:ℝ) := by
        simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) Real.exp_one_gt_two.le
  rw [neg_sub] at he
  have hc6 : sixthConstant ≤ (1/4096:ℝ) := by
    unfold sixthConstant
    norm_num
    linarith
  have hi : (1/18:ℝ) ≤ (6*Real.exp 1)⁻¹ := by
    have hh : 6 * Real.exp 1 ≤ (18:ℝ) := by linarith [Real.exp_one_lt_three]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ)<6*Real.exp 1) hh
  have hc3 : (1/5832:ℝ) ≤ cubicConstant := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/18) hi 3
    norm_num only at hh
    exact hh
  linarith

lemma sixth_of_cubic {a b B Y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hBm : B ≤ (a+b)/2) (hYm : Y ≤ (a+b)/2)
    (hcubic : cubicConstant * Y ^ 3 ≤ ((a+b)/2-B) * max a b ^ 2) :
    sixthConstant * Y ^ 6 ≤ (a^2+b^2-2*B^2) * (a^2+b^2)^2 := by
  let M := max a b
  let D := (a+b)/2-B
  let E := a^2+b^2-2*B^2
  let S := a^2+b^2
  have hM : 0 ≤ M := ha.trans (le_max_left _ _)
  have hMsum : M ≤ a+b := max_le (by linarith) (by linarith)
  have hD : 0 ≤ D := sub_nonneg.mpr hBm
  have hE : D*M ≤ E := by
    have hh := mul_nonneg hD (show 0 ≤ a+b-M by linarith)
    have hx := mul_nonneg hD hB
    dsimp [D,E] at *
    nlinarith [sq_nonneg (a-b)]
  have hEM : cubicConstant * Y^3 ≤ E*M := by
    apply hcubic.trans
    have hh := mul_le_mul_of_nonneg_right hE hM
    simpa only [M, pow_two, mul_assoc] using hh
  have hE0 : 0 ≤ E := (mul_nonneg hD hM).trans hE
  have hS : 0 ≤ S := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hMY : M*Y ≤ S := by
    have hh := mul_le_mul hMsum hYm hY (add_nonneg ha hb)
    dsimp [S]
    nlinarith [sq_nonneg (a-b)]
  have hY2 : 2*Y^2 ≤ S := by
    have hh := pow_le_pow_left₀ hY hYm 2
    dsimp [S]
    nlinarith [sq_nonneg (a-b)]
  have hSY : 2*M*Y^3 ≤ S^2 := by
    have hh := mul_le_mul hMY hY2 (by positivity) hS
    nlinarith
  calc
    sixthConstant * Y^6 ≤ (2*cubicConstant)*Y^6 :=
      mul_le_mul_of_nonneg_right sixthConstant_le_twice_cubic (by positivity)
    _ = (cubicConstant*Y^3)*(2*Y^3) := by ring
    _ ≤ (E*M)*(2*Y^3) := mul_le_mul_of_nonneg_right hEM (by positivity)
    _ = E*(2*M*Y^3) := by ring
    _ ≤ E*S^2 := mul_le_mul_of_nonneg_left hSY hE0

end VariableExponent

namespace VariableTree

open VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end VariableTree

namespace AggregationSpace

open UniformSpace VariableExponent

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end AggregationSpace

end RecursivePotentials

end

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.VariableExponent
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology


theorem solution : type_of% @_root_.OAI.RecursivePotentials.VariableExponent.sixth_of_cubic := @_root_.OAI.RecursivePotentials.VariableExponent.sixth_of_cubic
