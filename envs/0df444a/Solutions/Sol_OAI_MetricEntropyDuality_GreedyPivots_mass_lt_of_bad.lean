-- Prove2me | solution 1 for OAI.MetricEntropyDuality.GreedyPivots.mass_lt_of_bad
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:54:44.383813+00:00
-- url     : https://prove2.me/submissions/e0a01e0a-b304-42b2-b82d-01407d6f7393

import Mathlib
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

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.GreedyPivots
universe uX uY
open scoped BigOperators
variable {X : Type uX} {Y : Type uY}
variable [Nonempty X] [DecidableEq Y]
theorem h51b_mono (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) {k n : ℕ} (hk : k ≤ n) :
    covered μ I θ k ⊆ covered μ I θ n := by
  induction n, hk using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    exact ih.trans (by
      show covered μ I θ m ⊆ covered μ I θ m ∪ _
      exact Finset.subset_union_left)

theorem h51b_gain (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ) (k : ℕ)
    (hbad : ∃ x, θ < mass μ (I x \ covered μ I θ k)) :
    θ < mass μ (covered μ I θ (k + 1)) - mass μ (covered μ I θ k) := by
  have hp : θ < mass μ (I (choosePivot μ I θ (covered μ I θ k)) \ covered μ I θ k) := by
    unfold choosePivot
    rw [dif_pos hbad]
    exact hbad.choose_spec
  have : covered μ I θ (k + 1) = covered μ I θ k ∪
      (I (choosePivot μ I θ (covered μ I θ k)) \ covered μ I θ k) := by
    show _ ∪ _ = _
    rw [Finset.union_sdiff_self_eq_union]
  rw [this]
  unfold mass at hp ⊢
  rw [Finset.sum_union Finset.disjoint_sdiff]
  linarith

theorem solution (μ : Y → ℝ) (I : X → Finset Y) (θ : ℝ)
    (hμ : ∀ y, 0 ≤ μ y) (n : ℕ) :
    (∃ x, θ < mass μ (I x \ covered μ I θ n)) →
      n = 0 ∨ (n : ℝ) * θ < mass μ (covered μ I θ n) := by
  rintro ⟨x, hx⟩
  have hgain : ∀ k, k < n → θ < mass μ (covered μ I θ (k + 1)) - mass μ (covered μ I θ k) := by
    intro k hk
    refine h51b_gain μ I θ k ⟨x, lt_of_lt_of_le hx ?_⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.sdiff_subset_sdiff le_rfl (h51b_mono μ I θ hk.le)) (fun y _ _ => hμ y)
  have hz : mass μ (covered μ I θ 0) = 0 := by simp [mass]
  have key : ∀ m, m ≤ n → m = 0 ∨ (m : ℝ) * θ < mass μ (covered μ I θ m) := by
    intro m
    induction m with
    | zero => intro _; left; rfl
    | succ m ih =>
      intro hm
      right
      have g := hgain m (by omega)
      rcases ih (by omega) with h0 | h0
      · subst h0
        rw [hz] at g
        push_cast
        linarith
      · push_cast
        linarith
  exact key n le_rfl

