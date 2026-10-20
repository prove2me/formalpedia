-- Prove2me | solution 2 for OAI.MetricEntropyDuality.SymmetricForm.eval_contract
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:59:05.854186+00:00
-- url     : https://prove2.me/submissions/d750d700-567f-48db-9ee5-6e5277aebd12

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/FormContraction.lean:L69-L96
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.SymmetricForm.eval_contract. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.FormContraction ----
namespace OAI

universe uK

/-!
# Contraction of symmetric forms

The coefficients of a contraction are obtained by summing the original
coefficients against the fixed vector.  Evaluation is literally evaluation of
that original form with the vector in the first slot.  The proof reindexes all
ordered basis tuples, including repeated indices and the empty remaining tuple.
-/

namespace MetricEntropyDuality
namespace SymmetricForm

open scoped BigOperators

variable {K : Type uK} {r j : ℕ}

section CommSemiring

variable [CommSemiring K]

/-- Coefficient contraction agrees with inserting the fixed vector into evaluation. -/
theorem eval_contract (v : Fin r → K) (F : SymmetricForm K r (j + 1))
    (args : Fin j → (Fin r → K)) :
    eval (contract v F) args = eval F (Fin.cons v args) := by
  classical
  have hsplit : eval F (Fin.cons v args) =
      ∑ b : Fin r, ∑ a : Fin j → Fin r,
        F (Sym.cons b (tupleSym a)) * (v b * ∏ i, args i (a i)) := by
    unfold eval
    rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => Fin r)).sum_comp
      (fun a : Fin (j + 1) → Fin r => F (tupleSym a) *
        ∏ i : Fin (j + 1), (Fin.cons v args : Fin (j + 1) → (Fin r → K)) i (a i))]
    rw [Fintype.sum_prod_type]
    change (∑ b : Fin r, ∑ a : Fin j → Fin r,
      F (tupleSym (Fin.cons b a)) *
        ∏ i : Fin (j + 1), (Fin.cons v args : Fin (j + 1) → (Fin r → K)) i
          ((Fin.cons b a : Fin (j + 1) → Fin r) i)) = _
    simp only [tupleSym_cons, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [hsplit]
  change (∑ a : Fin j → Fin r,
    (∑ b : Fin r, v b * F (Sym.cons b (tupleSym a))) * ∏ i, args i (a i)) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ac_rfl

end CommSemiring

section CommRing

variable [CommRing K]

end CommRing

end SymmetricForm
end MetricEntropyDuality

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.SymmetricForm
open scoped BigOperators


theorem solution.{uK} : type_of% @_root_.OAI.MetricEntropyDuality.SymmetricForm.eval_contract.{uK} := @_root_.OAI.MetricEntropyDuality.SymmetricForm.eval_contract.{uK}
