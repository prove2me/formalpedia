-- Prove2me | solution 2 for OAI.MetricEntropyDuality.coeff_diagonalPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:56:03.478259+00:00
-- url     : https://prove2.me/submissions/db2ea1be-4680-4e51-8313-5bb4f85bff4c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FormPolynomials.lean:L126-L143
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.coeff_diagonalPolynomial. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.FormPolynomials ----
namespace OAI

universe uK

/-!
# Actual polynomials of symmetric forms

The definitions sum over ordered basis tuples, exactly as the multilinear
form evaluation does. The diagonal coefficient of a basis multiset is its
ordered-tuple fiber cardinality times the value of the form. This coefficient
is nonzero in characteristic greater than the degree. Renaming every vector
block to the same coordinate proves nonvanishing for every index tuple,
including tuples with repeated indices.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators
open MvPolynomial

/-- Passing from an ordered tuple to a monomial counts each occurrence. -/
theorem symExponent_tupleSym {r h : ℕ} (b : Fin h → Fin r) :
    symExponent (tupleSym b) = ∑ j : Fin h, Finsupp.single (b j) 1 := by
  simp only [symExponent, coe_tupleSym]
  induction h with
  | zero => simp
  | succ h ih =>
      rw [List.ofFn_succ, ← Multiset.cons_coe, ← Multiset.singleton_add,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, Fin.sum_univ_succ, ih]

private theorem diagonal_term_eq_monomial {K : Type uK} [CommSemiring K] {r h : ℕ}
    (F : SymmetricForm K r h) (b : Fin h → Fin r) :
    C (F (tupleSym b)) * (∏ j : Fin h, X (b j) : MvPolynomial (Fin r) K) =
      monomial (symExponent (tupleSym b)) (F (tupleSym b)) := by
  rw [symExponent_tupleSym]
  simpa only [MvPolynomial.X] using
    (monomial_sum_index (Finset.univ : Finset (Fin h))
      (fun j => Finsupp.single (b j) 1) (F (tupleSym b))).symm

/-- Distinct basis multisets yield distinct monomials. The coefficient is
exactly the ordered-tuple multiplicity, including every repeated basis index. -/
theorem coeff_diagonalPolynomial {K : Type uK} [CommSemiring K] {r h : ℕ}
    (F : SymmetricForm K r h) (s : Sym (Fin r) h) :
    (diagonalPolynomial F).coeff (symExponent s) = (symFiberCard s : K) * F s := by
  classical
  unfold diagonalPolynomial
  rw [coeff_sum]
  simp_rw [diagonal_term_eq_monomial, coeff_monomial, symExponent_eq_iff]
  calc
    (∑ b : Fin h → Fin r, if tupleSym b = s then F (tupleSym b) else 0) =
        ∑ b ∈ Finset.univ.filter (fun b : Fin h → Fin r => tupleSym b = s), F s := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : tupleSym b = s <;> simp [hb]
    _ = (symFiberCard s : K) * F s := by
      simp only [Finset.sum_const, nsmul_eq_mul, symFiberCard, Fintype.card_subtype]

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality
open scoped BigOperators
open MvPolynomial


theorem solution.{uK} : type_of% @_root_.OAI.MetricEntropyDuality.coeff_diagonalPolynomial.{uK} := @_root_.OAI.MetricEntropyDuality.coeff_diagonalPolynomial.{uK}
