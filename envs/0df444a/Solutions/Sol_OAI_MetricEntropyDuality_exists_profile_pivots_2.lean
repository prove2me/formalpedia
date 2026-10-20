-- Prove2me | solution 2 for OAI.MetricEntropyDuality.exists_profile_pivots
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:12:20.385221+00:00
-- url     : https://prove2.me/submissions/9f448b6b-71f1-453f-a189-6b9917e65276

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/ProfilePivots.lean:L24-L57
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.exists_profile_pivots. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.List.FinRange
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Definitions.Def_MetricEntropyDuality
import Definitions.Def_OAI_Analysis_MetricEntropy_FormDimension
import Definitions.Def_OAI_Analysis_MetricEntropy_Parameters
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricIndex
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricForms
import Definitions.Def_OAI_Analysis_MetricEntropy_Basic
import Definitions.Def_OAI_Analysis_MetricEntropy_EntropyPair
import Definitions.Def_OAI_Analysis_MetricEntropy_SupportPolar
import Definitions.Def_OAI_Analysis_MetricEntropy_PolarCover
import Definitions.Def_OAI_Analysis_MetricEntropy_CoordinateTransport
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionTuples
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteProductCounting
import Definitions.Def_OAI_Analysis_MetricEntropy_DirectionSampling
import Definitions.Def_OAI_Analysis_MetricEntropy_SymmetricMultiplicity
import Definitions.Def_OAI_Analysis_MetricEntropy_FormPolynomials
import Definitions.Def_OAI_Analysis_MetricEntropy_PolynomialZeroBound
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Theorems.Thm_OAI_MetricEntropyDuality_exists_common_index
import Theorems.Thm_OAI_MetricEntropyDuality_exists_greedy_pivots

-- ---- from OAI.Analysis.MetricEntropy.ProfilePivots ----
namespace OAI

universe uX uY uLabel

/-!
# A common index and greedy pivots at every profile level

The retained index is chosen once from the column weights. At each level,
the bounded greedy construction is applied to the actual retained graph
balls. All assignments and residual bounds below are consequently proved
for the actual partition graphs.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators Classical

/-- One common retained index and an actual bounded pivot assignment at each
of the finitely many profile levels. -/
theorem exists_profile_pivots {X : Type uX} {Y : Type uY}
    [Fintype X] [Nonempty X] [Fintype Y]
    {u : ℕ} {Label : Fin u → Type uLabel}
    (L : (i : Fin u) → X → Label i) (v : Y → X) (T : Y → Finset (Fin u))
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1)
    (hu : 0 < u) (θ : ℝ) (hθ : 0 < θ) (s : ℕ) (hs : 1 ≤ (s : ℝ) * θ)
    (hcomp : ∀ y, ((Finset.univ \ T y).card : ℝ) ≤ θ * (u : ℝ)) (h : ℕ) :
    ∃ i : Fin u, ∃ centers : Fin h → Fin s → X,
      ∃ assigned : Fin h → Y → Option (Fin s),
        (∑ y ∈ Finset.univ.filter (fun y => i ∉ T y), μ y) ≤ θ ∧
        (∀ j y k, assigned j y = some k →
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val (centers j k) (v y)) ∧
        (∀ j x, (∑ y ∈ Finset.univ.filter (fun y =>
          i ∈ T y ∧ PartitionGraph.near L (T y) j.val x (v y) ∧
            assigned j y = none), μ y) ≤ θ) := by
  classical
  obtain ⟨i, hi⟩ := exists_common_index hu T μ hμ hmass hθ.le hcomp
  let incidence : Fin h → X → Finset Y := fun j x =>
    Finset.univ.filter (fun y => i ∈ T y ∧ PartitionGraph.near L (T y) j.val x (v y))
  have hgreedy (j : Fin h) :=
    exists_greedy_pivots μ (incidence j) hμ hmass θ hθ s hs
  let centers : Fin h → Fin s → X := fun j => (hgreedy j).choose
  let assigned : Fin h → Y → Option (Fin s) := fun j => (hgreedy j).choose_spec.choose
  refine ⟨i, centers, assigned, hi, ?_, ?_⟩
  · intro j y k hy
    have hyI : y ∈ incidence j (centers j k) :=
      (hgreedy j).choose_spec.choose_spec.1 y k hy
    exact (Finset.mem_filter.mp hyI).2
  · intro j x
    have hres : (∑ y ∈ (incidence j x).filter (fun y => assigned j y = none), μ y) ≤ θ :=
      (hgreedy j).choose_spec.choose_spec.2.2 x
    simpa only [incidence, Finset.filter_filter, and_assoc] using hres

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators Classical


theorem solution.{uX,uY,uLabel} : type_of% @_root_.OAI.MetricEntropyDuality.exists_profile_pivots.{uX,uY,uLabel} := @_root_.OAI.MetricEntropyDuality.exists_profile_pivots.{uX,uY,uLabel}
