-- Prove2me | solution 1 for OAI.Dixmier.equal_coboundaries_iff_commute_sub
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:51:56.965957+00:00
-- url     : https://prove2.me/submissions/ee3a3cea-431d-4832-b658-459df9085ba1

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Cocycle.lean:L49-L64
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.equal_coboundaries_iff_commute_sub. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle

-- ---- from OAI.Analysis.Unitarizability.Cocycle ----
namespace OAI

/-! Cocycle algebra in an arbitrary ring, specializing to bounded complex Hilbert-space operators. -/
namespace Dixmier
section Ring
variable {G R : Type*} [Group G] [Ring R]

theorem conjugate_sub (U : G →* R) (g : G) (A B : R) :
    conjugate U g (A - B) = conjugate U g A - conjugate U g B := by
  simp [conjugate, mul_sub, sub_mul]

theorem conjugate_eq_self_iff_commute (U : G →* R) (g : G) (T : R) :
    conjugate U g T = T ↔ Commute (U g) T := by
  have hinv : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  have hginv : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  constructor
  · intro h
    have hh := congrArg (fun x : R => x * U g) h
    change U g * T = T * U g
    simpa [conjugate, mul_assoc, hinv] using hh
  · intro h
    change U g * T * U g⁻¹ = T
    rw [h.eq, mul_assoc, hginv, mul_one]

/-- Comparing the two implementers gives the commutant element T - B. -/
theorem equal_coboundaries_iff_commute_sub (U : G →* R) (T B : R) (g : G) :
    coboundary U T g = coboundary U B g ↔ Commute (U g) (T - B) := by
  rw [← conjugate_eq_self_iff_commute, conjugate_sub]
  simp only [coboundary]
  constructor
  · intro h
    calc
      conjugate U g T - conjugate U g B =
          (T - (T - conjugate U g T)) - (B - (B - conjugate U g B)) := by abel
      _ = T - B := by rw [h]; abel
  · intro h
    calc
      T - conjugate U g T = B - conjugate U g B +
          ((T - B) - (conjugate U g T - conjugate U g B)) := by abel
      _ = B - conjugate U g B := by rw [h]; abel

end Ring
end Dixmier

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
variable {G R : Type*} [Group G] [Ring R]

theorem solution (U : G →* R) (T B : R) (g : G) :
    coboundary U T g = coboundary U B g ↔ Commute (U g) (T - B) := by
  first
    | exact OAI.Dixmier.equal_coboundaries_iff_commute_sub U T B g
    | exact OAI.Dixmier.equal_coboundaries_iff_commute_sub
    | (apply OAI.Dixmier.equal_coboundaries_iff_commute_sub <;> assumption)
    | (intros; apply OAI.Dixmier.equal_coboundaries_iff_commute_sub <;> assumption)
