-- Prove2me | solution 1 for OAI.MetricEntropyDuality.polynomial_zero_card_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:35:07.831247+00:00
-- url     : https://prove2.me/submissions/424a6408-79c4-41f1-9f15-f3d0a605c64e

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

open OAI OAI.MetricEntropyDuality
universe uV
variable {p : ℕ} [Fact p.Prime]


theorem solution {V : Type uV} [Fintype V]
    (P : MvPolynomial V (ZMod p)) (hP : P ≠ 0) :
    p * (polynomialZeros P).card ≤ P.totalDegree * p ^ Fintype.card V := by
  classical
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  have hP' : MvPolynomial.rename e P ≠ 0 := by
    intro h
    apply hP
    exact MvPolynomial.rename_injective e e.injective (by simpa using h)
  have hdeg : (MvPolynomial.rename e P).totalDegree ≤ P.totalDegree :=
    MvPolynomial.totalDegree_rename_le e P
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hP' (Finset.univ : Finset (ZMod p))
  have hcard : (Finset.univ.filter fun f : Fin (Fintype.card V) → ZMod p =>
      MvPolynomial.eval f (MvPolynomial.rename e P) = 0).card = (polynomialZeros P).card := by
    refine Finset.card_bij (fun f _ => f ∘ e) ?_ ?_ ?_
    · intro f hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf
      rw [mem_polynomialZeros]
      simpa [MvPolynomial.eval_rename] using hf
    · intro f _ g _ hfg
      funext i
      have := congrFun hfg (e.symm i)
      simpa using this
    · intro x hx
      rw [mem_polynomialZeros] at hx
      refine ⟨x ∘ e.symm, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [MvPolynomial.eval_rename]
        have hc : (x ∘ e.symm) ∘ e = x := by
          funext v
          simp
        rw [hc]
        exact hx
      · funext v
        simp
  simp only [Fintype.piFinset_univ, Finset.card_univ, ZMod.card] at hsz
  rw [hcard] at hsz
  have hp0 : (0 : NNRat) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [div_le_div_iff₀ (by positivity) hp0] at hsz
  have h1 : (((polynomialZeros P).card * p : ℕ) : NNRat) ≤
      (((MvPolynomial.rename e P).totalDegree * p ^ Fintype.card V : ℕ) : NNRat) := by
    push_cast
    exact hsz
  have h2 := Nat.cast_le.mp h1
  calc p * (polynomialZeros P).card = (polynomialZeros P).card * p := Nat.mul_comm _ _
    _ ≤ (MvPolynomial.rename e P).totalDegree * p ^ Fintype.card V := h2
    _ ≤ P.totalDegree * p ^ Fintype.card V := Nat.mul_le_mul_right _ hdeg

