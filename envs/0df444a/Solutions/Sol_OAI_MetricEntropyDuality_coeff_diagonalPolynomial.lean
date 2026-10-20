-- Prove2me | solution 1 for OAI.MetricEntropyDuality.coeff_diagonalPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:31:43.189272+00:00
-- url     : https://prove2.me/submissions/e144c109-bda2-4f67-94b0-6af55c614b3b

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

open OAI OAI.MetricEntropyDuality
universe uK
open scoped BigOperators
open MvPolynomial
lemma h51m_toFinsupp {r : ℕ} : ∀ {h : ℕ} (b : Fin h → Fin r),
    Multiset.toFinsupp ((List.ofFn b : List (Fin r)) : Multiset (Fin r)) = ∑ j, Finsupp.single (b j) 1
  | 0, b => by simp
  | h+1, b => by
    rw [List.ofFn_succ, ← Multiset.cons_coe, Fin.sum_univ_succ, ← h51m_toFinsupp (fun i => b i.succ)]
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, Multiset.toFinsupp_singleton]

lemma h51m_prodX {K : Type*} [CommSemiring K] {r h : ℕ} (b : Fin h → Fin r) :
    (∏ j : Fin h, (MvPolynomial.X (b j) : MvPolynomial (Fin r) K)) =
      MvPolynomial.monomial (symExponent (tupleSym b)) 1 := by
  simp only [MvPolynomial.X, symExponent, coe_tupleSym, h51m_toFinsupp]
  rw [MvPolynomial.monomial_sum_one]

theorem solution {K : Type uK} [CommSemiring K] {r h : ℕ}
    (F : SymmetricForm K r h) (s : Sym (Fin r) h) :
    (diagonalPolynomial F).coeff (symExponent s) = (symFiberCard s : K) * F s := by
  classical
  unfold diagonalPolynomial
  rw [MvPolynomial.coeff_sum]
  simp_rw [h51m_prodX, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_monomial, symExponent_eq_iff]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have : ∀ b ∈ Finset.univ.filter (fun b : Fin h → Fin r => tupleSym b = s), F (tupleSym b) = F s := by
    intro b hb; simp at hb; rw [hb]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  congr 1
  unfold symFiberCard
  rw [Fintype.card_subtype]

