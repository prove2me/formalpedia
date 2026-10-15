-- Prove2me | solution 1 for OAI.Dixmier.kernel_energy_ge_card
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T01:45:17.55323+00:00
-- url     : https://prove2.me/submissions/99b6ceb3-8296-4893-9161-496741682991

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/KernelEnergy.lean:L105-L118
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.kernel_energy_ge_card. The node keeps its source
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
import Theorems.Thm_OAI_Dixmier_rankOne_sum_energy

-- ---- from OAI.Analysis.Unitarizability.KernelEnergy ----
namespace OAI

/-! Positive rank-one kernel energy. Matrices are represented by their entries
with the unnormalized Hilbert–Schmidt (Euclidean coefficient) norm. -/
noncomputable section
namespace Dixmier
attribute [local instance] Classical.propDecidable
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

omit [Fintype K] in
theorem kernelCoefficients_offsupport (v : I → EuclideanSpace ℂ K) (s : I → G)
    {g : G} (hg : g ∉ Finset.univ.image s) : kernelCoefficients v s g = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i hi
  exact (hg (Finset.mem_image.mpr ⟨i, mem_univ _, (mem_filter.mp hi).2⟩)).elim

/-- The kernel-energy lower bound preserves every colliding product label. -/
theorem kernel_energy_ge_card (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (s : I → G) : (Fintype.card I : ℝ) ≤ ∑' g, ‖kernelCoefficients v s g‖^2 := by
  classical
  rw [tsum_eq_sum (s := Finset.univ.image s) (fun g hg => by
    simp [kernelCoefficients_offsupport v s hg])]
  have hc := congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_eq_sum_card_image s Finset.univ)
  simp only [Finset.card_univ, Nat.cast_sum] at hc
  calc
    (Fintype.card I : ℝ) = ∑ g ∈ Finset.univ.image s, ((Finset.univ.filter fun i => s i = g).card : ℝ) := hc
    _ ≤ ∑ g ∈ Finset.univ.image s, ‖kernelCoefficients v s g‖^2 := by
      apply Finset.sum_le_sum
      intro g hg
      exact rankOne_sum_energy v hv _

end Dixmier

end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier
attribute [local instance] Classical.propDecidable
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

theorem solution (v : I → EuclideanSpace ℂ K) (hv : ∀ i, ‖v i‖ = 1)
    (s : I → G) : (Fintype.card I : ℝ) ≤ ∑' g, ‖kernelCoefficients v s g‖^2 := by
  first
    | exact OAI.Dixmier.kernel_energy_ge_card v hv s
    | exact OAI.Dixmier.kernel_energy_ge_card
    | (apply OAI.Dixmier.kernel_energy_ge_card <;> assumption)
    | (intros; apply OAI.Dixmier.kernel_energy_ge_card <;> assumption)
