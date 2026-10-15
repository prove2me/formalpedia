-- Prove2me | solution 1 for OAI.Dixmier.FrameParameters.bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:46:34.755754+00:00
-- url     : https://prove2.me/submissions/04c22c9b-ad57-4e4b-ba6f-ef3d0b098615

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FrameParameters.lean:L14-L37
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.FrameParameters.bounds. The node keeps its source
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

theorem bounds {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    1 ≤ dimension n r ∧ subfamilySize n r ≤ dimension n r ∧
      (subfamilySize n r : ℝ) * Real.log n ≤ dimension n r := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : 1 < Real.log (2 * (n : ℝ)) := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by positivity)]
    linarith [Real.exp_one_lt_three]
  have hceil : 2 * (r : ℝ) * Real.log (2 * (n : ℝ)) ≤ dimension n r := Nat.le_ceil _
  have hp : (subfamilySize n r : ℝ) ≤ 2 * r := by exact_mod_cast Nat.min_le_left (2*r) n
  have hlogn : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) := Real.log_le_log hn0 (by linarith)
  have hp0 : (0 : ℝ) ≤ subfamilySize n r := Nat.cast_nonneg _
  have hkp : (subfamilySize n r : ℝ) ≤ dimension n r := by
    have hp2 := mul_le_mul_of_nonneg_left hlog.le (by positivity : (0 : ℝ) ≤ 2 * r)
    nlinarith
  refine ⟨?_, by exact_mod_cast hkp, ?_⟩
  · have : (1 : ℝ) ≤ dimension n r := by nlinarith
    exact_mod_cast this
  · calc
      _ ≤ (subfamilySize n r : ℝ) * Real.log (2 * (n : ℝ)) := mul_le_mul_of_nonneg_left hlogn hp0
      _ ≤ 2 * (r : ℝ) * Real.log (2 * (n : ℝ)) := mul_le_mul_of_nonneg_right hp (by linarith)
      _ ≤ _ := hceil

end FrameParameters
end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.FrameParameters

theorem solution {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r) :
    1 ≤ dimension n r ∧ subfamilySize n r ≤ dimension n r ∧
      (subfamilySize n r : ℝ) * Real.log n ≤ dimension n r := by
  first
    | exact OAI.Dixmier.FrameParameters.bounds hn hr
    | exact OAI.Dixmier.FrameParameters.bounds
    | (apply OAI.Dixmier.FrameParameters.bounds <;> assumption)
    | (intros; apply OAI.Dixmier.FrameParameters.bounds <;> assumption)
