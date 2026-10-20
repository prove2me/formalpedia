-- Prove2me | solution 2 for OAI.MetricEntropyDuality.GreedyPivots.mass_lt_of_bad
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:08:52.664717+00:00
-- url     : https://prove2.me/submissions/2c78bfab-5546-4ecf-86e8-6298fc1d0de8

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/GreedyPivots.lean:L96-L122
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.GreedyPivots.mass_lt_of_bad. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.GreedyPivots ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
namespace OAI

universe uX uY

/-!
# A bounded greedy family of pivots

At each step, choose a set whose mass outside the current union exceeds the
threshold if such a set exists. Otherwise choose a fixed padding center.
Padding still enlarges the union, so it cannot increase any residual mass.
If the residual bound failed after `s` steps, all preceding steps would have
made a strict gain greater than the threshold, contradicting total mass at
most one and `1 ≤ s * θ`.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

namespace GreedyPivots

variable {X : Type uX} {Y : Type uY}

theorem mass_mono (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    {U V : Finset Y} (hUV : U ⊆ V) : mass μ U ≤ mass μ V :=
  Finset.sum_le_sum_of_subset_of_nonneg hUV (fun y _ _ => hμ y)

variable [Nonempty X] [DecidableEq Y]

theorem choosePivot_spec (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (U : Finset Y)
    (h : ∃ x, θ < mass μ (I x \ U)) :
    θ < mass μ (I (choosePivot μ I θ U) \ U) := by
  classical
  simpa only [choosePivot, dite_eq_left h] using h.choose_spec

theorem covered_subset_succ (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (n : ℕ) :
    covered μ I θ n ⊆ covered μ I θ (n + 1) := Finset.subset_union_left

omit [Nonempty X] in
theorem bad_of_subset (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ)
    (hμ : ∀ y, 0 ≤ μ y) {U V : Finset Y} (hUV : U ⊆ V)
    (hV : ∃ x, θ < mass μ (I x \ V)) : ∃ x, θ < mass μ (I x \ U) := by
  obtain ⟨x, hx⟩ := hV
  refine ⟨x, hx.trans_le (mass_mono μ hμ ?_)⟩
  intro y hy
  obtain ⟨hyI, hyV⟩ := Finset.mem_sdiff.mp hy
  exact Finset.mem_sdiff.mpr ⟨hyI, fun hyU => hyV (hUV hyU)⟩

theorem mass_union (μ : Y → ℝ) (U V : Finset Y) :
    mass μ (U ∪ V) = mass μ U + mass μ (V \ U) := by
  calc
    mass μ (U ∪ V) = mass μ (U ∪ (V \ U)) :=
      congrArg (mass μ) Finset.union_sdiff_self_eq_union.symm
    _ = mass μ U + mass μ (V \ U) := Finset.sum_union Finset.disjoint_sdiff

theorem mass_covered_succ (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (n : ℕ) :
    mass μ (covered μ I θ (n + 1)) = mass μ (covered μ I θ n) +
      mass μ (I (choosePivot μ I θ (covered μ I θ n)) \ covered μ I θ n) :=
  mass_union μ _ _

/-- A residual violation at a positive stage forces strict total mass growth
at every earlier stage, including the last one. -/
theorem mass_lt_of_bad (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (n : ℕ) :
    (∃ x, θ < mass μ (I x \ covered μ I θ n)) →
      n = 0 ∨ (n : ℝ) * θ < mass μ (covered μ I θ n) := by
  induction n with
  | zero =>
      intro _
      exact Or.inl rfl
  | succ n ih =>
      intro hbad
      have hprev := bad_of_subset μ I θ hμ (covered_subset_succ μ I θ n) hbad
      have hlower : (n : ℝ) * θ ≤ mass μ (covered μ I θ n) := by
        rcases ih hprev with hzero | hlt
        · subst n
          simp [mass]
        · exact hlt.le
      have hgain := choosePivot_spec μ I θ (covered μ I θ n) hprev
      right
      calc
        ((n + 1 : ℕ) : ℝ) * θ = (n : ℝ) * θ + θ := by
          simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        _ < mass μ (covered μ I θ n) +
            mass μ (I (choosePivot μ I θ (covered μ I θ n)) \ covered μ I θ n) :=
          add_lt_add_of_le_of_lt hlower hgain
        _ = mass μ (covered μ I θ (n + 1)) := (mass_covered_succ μ I θ n).symm

end GreedyPivots

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.GreedyPivots
open scoped BigOperators


theorem solution.{uX,uY} : type_of% @_root_.OAI.MetricEntropyDuality.GreedyPivots.mass_lt_of_bad.{uX,uY} := @_root_.OAI.MetricEntropyDuality.GreedyPivots.mass_lt_of_bad.{uX,uY}
