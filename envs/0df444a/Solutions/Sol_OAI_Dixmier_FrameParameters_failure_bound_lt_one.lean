-- Prove2me | solution 1 for OAI.Dixmier.FrameParameters.failure_bound_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:47:12.423134+00:00
-- url     : https://prove2.me/submissions/6c50ef9c-11bf-4979-820f-fa08ffe32d3b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FrameParameters.lean:L39-L68
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.FrameParameters.failure_bound_lt_one. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters

-- ---- from OAI.Analysis.Unitarizability.FrameParameters ----
namespace OAI

/-! Ceiling dimensions and finite union-bound arithmetic for frames. -/
noncomputable section
namespace Dixmier
namespace FrameParameters

/-- The frame failure probability is strictly below one. -/
theorem failure_bound_lt_one {n k p : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hp : p ≤ k) (hplog : (p : ℝ) * Real.log n ≤ k) :
    2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpk : (p : ℝ) ≤ k := by exact_mod_cast hp
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl9 : Real.log 9 ≤ 4 := by
    have h3 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    have h9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9 : ℝ) = 3^2 by norm_num, Real.log_pow]
      norm_num
    rw [h9]
    linarith
  have he : Real.log 2 + (p : ℝ)*Real.log n + ((k : ℝ)+p)*Real.log 9 -25*(k : ℝ)/2 < 0 := by
    have hh := mul_le_mul_of_nonneg_left hl9 (by positivity : (0 : ℝ) ≤ (k : ℝ)+p)
    nlinarith
  have hid : 2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) =
      Real.exp (Real.log 2 + (p : ℝ)*Real.log n + ((k : ℝ)+p)*Real.log 9 -25*(k : ℝ)/2) := by
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_add]
    simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Real.exp_nat_mul,
      Real.exp_log hn0, ← Nat.cast_add]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 9)]
    congr 1
    ring_nf
  rw [hid]
  exact Real.exp_lt_one_iff.mpr he

end FrameParameters
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.FrameParameters

theorem solution {n k p : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k)
    (hp : p ≤ k) (hplog : (p : ℝ) * Real.log n ≤ k) :
    2 * (n : ℝ)^p * 9^(k+p) * Real.exp (-25*(k : ℝ)/2) < 1 := by
  first
    | exact OAI.Dixmier.FrameParameters.failure_bound_lt_one hn hk hp hplog
    | exact OAI.Dixmier.FrameParameters.failure_bound_lt_one
    | (apply OAI.Dixmier.FrameParameters.failure_bound_lt_one <;> assumption)
    | (intros; apply OAI.Dixmier.FrameParameters.failure_bound_lt_one <;> assumption)
