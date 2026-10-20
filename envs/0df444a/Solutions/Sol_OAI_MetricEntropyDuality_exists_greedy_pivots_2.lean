-- Prove2me | solution 2 for OAI.MetricEntropyDuality.exists_greedy_pivots
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:11:25.93875+00:00
-- url     : https://prove2.me/submissions/232c3dbf-bcbc-4131-9f07-9fc12a12dddd

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/GreedyPivots.lean:L160-L213
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.exists_greedy_pivots. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_GreedyPivots_mass_lt_of_bad
import Theorems.Thm_OAI_MetricEntropyDuality_GreedyPivots_mem_covered_iff

-- ---- from OAI.Analysis.MetricEntropy.GreedyPivots ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

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

theorem residual_le [Fintype Y] (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (hmass : ∑ y, μ y ≤ 1) (s : ℕ)
    (hs : 1 ≤ (s : ℝ) * θ) (x : X) :
    mass μ (I x \ covered μ I θ s) ≤ θ := by
  have hs0 : s ≠ 0 := by
    intro hz
    subst s
    simp only [Nat.cast_zero, zero_mul] at hs
    exact (not_le_of_gt (zero_lt_one : (0 : ℝ) < 1)) hs
  apply le_of_not_gt
  intro hbad
  have hlower := mass_lt_of_bad μ I θ hμ s ⟨x, hbad⟩
  have hstrict := hlower.resolve_left hs0
  have hupper : mass μ (covered μ I θ s) ≤ 1 :=
    (mass_mono μ hμ (Finset.subset_univ _)).trans hmass
  exact (not_lt_of_ge hs) (hstrict.trans_le hupper)

end GreedyPivots

/-- A finite family has a bounded number of pivots whose uncovered mass is
uniformly small. The assignment is supported exactly on the union of their
sets, and assigns a column only to a set containing it. -/
theorem exists_greedy_pivots {X : Type uX} {Y : Type uY} [Fintype X] [Nonempty X] [Fintype Y]
    (μ : Y → ℝ) (I : X → Finset Y) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) (θ : ℝ) (_hθ : 0 < θ) (s : ℕ)
    (hs : 1 ≤ (s : ℝ) * θ) :
    ∃ centers : Fin s → X, ∃ assigned : Y → Option (Fin s),
      (∀ y k, assigned y = some k → y ∈ I (centers k)) ∧
      (∀ y, (∃ k, y ∈ I (centers k)) ↔ assigned y ≠ none) ∧
      (∀ x, ∑ y ∈ (I x).filter (fun y => assigned y = none), μ y ≤ θ) := by
  classical
  let centers : Fin s → X := fun k =>
    GreedyPivots.choosePivot μ I θ (GreedyPivots.covered μ I θ k.val)
  let assigned : Y → Option (Fin s) := fun y =>
    if h : ∃ k, y ∈ I (centers k) then some h.choose else none
  have hmem : ∀ y k, assigned y = some k → y ∈ I (centers k) := by
    intro y k hk
    by_cases hy : ∃ j, y ∈ I (centers j)
    · have heq : hy.choose = k := by
        apply Option.some.inj
        simpa only [assigned, dite_eq_left hy] using hk
      exact heq ▸ hy.choose_spec
    · simp only [assigned, dite_eq_right hy] at hk
      cases hk
  have hsupport : ∀ y, (∃ k, y ∈ I (centers k)) ↔ assigned y ≠ none := by
    intro y
    by_cases hy : ∃ k, y ∈ I (centers k) <;> simp [assigned, hy]
  have hcovered : ∀ y, y ∈ GreedyPivots.covered μ I θ s ↔
      ∃ k, y ∈ I (centers k) := by
    intro y
    rw [GreedyPivots.mem_covered_iff]
    constructor
    · rintro ⟨k, hk, hy⟩
      exact ⟨⟨k, hk⟩, hy⟩
    · rintro ⟨k, hy⟩
      exact ⟨k.val, k.isLt, hy⟩
  have hnone : ∀ y, assigned y = none ↔ y ∉ GreedyPivots.covered μ I θ s := by
    intro y
    constructor
    · intro hn hy
      exact ((hsupport y).mp ((hcovered y).mp hy)) hn
    · intro hy
      by_cases hn : assigned y = none
      · exact hn
      · exact (hy ((hcovered y).mpr ((hsupport y).mpr hn))).elim
  refine ⟨centers, assigned, hmem, hsupport, ?_⟩
  intro x
  have hfilter : (I x).filter (fun y => assigned y = none) =
      I x \ GreedyPivots.covered μ I θ s := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_sdiff, hnone]
  rw [hfilter]
  exact GreedyPivots.residual_le μ I θ hμ hmass s hs x

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators


theorem solution.{uX,uY} : type_of% @_root_.OAI.MetricEntropyDuality.exists_greedy_pivots.{uX,uY} := @_root_.OAI.MetricEntropyDuality.exists_greedy_pivots.{uX,uY}
