-- Prove2me | solution 1 for OAI.RecursivePotentials.AggregationSpace.lp_comparisons
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T09:14:36.421987+00:00
-- url     : https://prove2.me/submissions/6dcea134-9e5a-4505-a280-611383080c0f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/RecursivePotentials/VariableLp.lean:L293-L312
-- (upload_full_project.md Phase 4): solution for node OAI.RecursivePotentials.AggregationSpace.lp_comparisons. The node keeps its source
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
import Definitions.Def_OAI_Analysis_RecursivePotentials_VariableLp

-- ---- from OAI.Analysis.RecursivePotentials.VariableLp ----
namespace OAI

universe uIndex uSpace uOther uDomain uTarget uFiber

open scoped BigOperators

namespace RecursivePotentials

open Filter Topology

open Filter Topology

open scoped ENNReal

open UniformSpace

open Filter

open scoped Topology

open Filter Topology TopologicalSpace

open scoped ENNReal

noncomputable section

namespace LpSupport

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (E : ι → Type uFiber)
  [∀ i, NormedAddCommGroup (E i)] [fiberNormedSpace : ∀ i, NormedSpace ℝ (E i)]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

end LpSupport

namespace PowerExponent

end PowerExponent

namespace ScalarLp

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι]

variable (p q : PowerExponent) (hpq : p.val.HolderConjugate q.val)

include hpq

end ScalarLp

end

namespace AggregationVector

noncomputable section

open scoped ENNReal

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

end

end AggregationVector

namespace AggregationSpace

noncomputable section

open AggregationVector

variable {ι : Type uIndex} [indexDecidable : DecidableEq ι] (T : FiniteRootedTree ι)
    (e : ChildExponent)

lemma lpEquiv_coe (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (v : AggregationVector T e) :
    lpEquiv T e hp hstep h hh (v : AggregationSpace T e) = toLpLinear T e v :=
  ContinuousLinearMap.fromCompletion_apply_coe _ v

theorem lp_comparisons (hp : 1 < e.val)
    (hstep : ∀ c, c ≠ T.root → T.depth c = T.depth (T.parent c) + 1)
    (h : ℕ) (hh : ∀ s, T.depth s ≤ h) (x : AggregationSpace T e) :
    (h+1:ℝ)^(-1/e.val)*‖lpEquiv T e hp hstep h hh x‖ ≤ ‖x‖ ∧
      ‖x‖ ≤ 2*(h+1:ℝ)^(1-1/e.val)*‖lpEquiv T e hp hstep h hh x‖ := by
  have hboth : ‖x‖ ≤ 2*(h+1:ℝ)^(1-1/e.val)*‖lpEquiv T e hp hstep h hh x‖ ∧
      ‖lpEquiv T e hp hstep h hh x‖ ≤ (h+1:ℝ)^(1/e.val)*‖x‖ := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact (isClosed_le continuous_norm
        (continuous_const.mul (lpEquiv T e hp hstep h hh).continuous.norm)).inter
        (isClosed_le (lpEquiv T e hp hstep h hh).continuous.norm
          (continuous_const.mul continuous_norm))
    | ih v => simpa only [lpEquiv_coe,UniformSpace.Completion.norm_coe] using
        AggregationVector.lp_comparisons T e hp hstep h hh v
  refine ⟨?_,hboth.1⟩
  have hl := mul_le_mul_of_nonneg_left hboth.2 (Real.rpow_nonneg (by positivity : (0:ℝ)≤h+1) (-1/e.val))
  have he : (h+1:ℝ)^(-1/e.val) * (h+1:ℝ)^(1/e.val) = 1 := by
    rw [← Real.rpow_add (by positivity : (0:ℝ)<h+1),show -1/e.val+1/e.val=0 by ring,Real.rpow_zero]
  rwa [← mul_assoc,he,one_mul] at hl

end

end AggregationSpace

end RecursivePotentials

end OAI

-- ---- platform node ----
open OAI OAI.RecursivePotentials OAI.RecursivePotentials.AggregationSpace
open scoped BigOperators
open Filter Topology
open Filter Topology
open scoped ENNReal
open UniformSpace
open Filter
open scoped Topology
open Filter Topology TopologicalSpace
open scoped ENNReal
open AggregationVector


theorem solution.{uIndex} : type_of% @_root_.OAI.RecursivePotentials.AggregationSpace.lp_comparisons.{uIndex} := @_root_.OAI.RecursivePotentials.AggregationSpace.lp_comparisons.{uIndex}
