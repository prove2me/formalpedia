-- Prove2me | solution 1 for OAI.MetricEntropyDuality.exists_coefficient_representatives
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:33:57.55497+00:00
-- url     : https://prove2.me/submissions/747aee26-af1b-47e4-80ae-ce3018c3e856

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

open OAI OAI.MetricEntropyDuality
universe uX uY
open scoped BigOperators Pointwise
variable {X : Type uX} {Y : Type uY} [Fintype Y]


theorem solution (g : Y → X → ℝ) (ε : ℝ)
    (A : Finset (RealSpace X)) (hA : UniformApproximation g ε A) :
    ∃ centers : Fin A.card → RealSpace Y,
      (∀ j, centers j ∈ l1Ball Y) ∧
      ∀ lam ∈ l1Ball Y, ∃ j,
        UniformClose (2 * ε) (columnCombination g lam) (columnCombination g (centers j)) ∧
        l1Norm (lam - centers j) ≤ 2 := by
  classical
  let rep : RealSpace X → RealSpace Y := fun a =>
    if h : ∃ lam ∈ l1Ball Y, UniformClose ε (columnCombination g lam) a then h.choose else 0
  have hrep_mem : ∀ a, rep a ∈ l1Ball Y := by
    intro a
    simp only [rep]
    split_ifs with h
    · exact h.choose_spec.1
    · exact zero_mem_l1Ball
  refine ⟨fun j => rep (A.equivFin.symm j), fun j => hrep_mem _, ?_⟩
  intro lam hlam
  obtain ⟨a, haA, hla⟩ := hA lam hlam
  have hex : ∃ lam ∈ l1Ball Y, UniformClose ε (columnCombination g lam) a := ⟨lam, hlam, hla⟩
  have hra : rep a = hex.choose := by simp only [rep, dif_pos hex]
  refine ⟨A.equivFin ⟨a, haA⟩, ?_, ?_⟩
  · simp only [Equiv.symm_apply_apply]
    rw [hra]
    have h2 := hex.choose_spec.2
    intro x
    have e1 := hla x
    have e2 := h2 x
    calc |columnCombination g lam x - columnCombination g hex.choose x|
        = |(columnCombination g lam x - a x) - (columnCombination g hex.choose x - a x)| := by
          congr 1; ring
      _ ≤ |columnCombination g lam x - a x| + |columnCombination g hex.choose x - a x| :=
          abs_sub _ _
      _ ≤ 2 * ε := by linarith
  · simp only [Equiv.symm_apply_apply]
    have hm := hrep_mem a
    simp only [l1Ball, l1Norm, Set.mem_setOf_eq] at hm hlam ⊢
    calc ∑ i, |(lam - rep a) i| ≤ ∑ i, (|lam i| + |rep a i|) :=
          Finset.sum_le_sum (fun i _ => by simpa using abs_sub (lam i) (rep a i))
      _ ≤ 2 := by rw [Finset.sum_add_distrib]; linarith

