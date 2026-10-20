-- Prove2me | solution 2 for OAI.MetricEntropyDuality.SymmetricForm.eval_basis
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:41:28.58944+00:00
-- url     : https://prove2.me/submissions/1aab7233-0e20-4874-a8e3-15b341efa376

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/SymmetricForms.lean:L66-L82
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.SymmetricForm.eval_basis. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.SymmetricForms ----
namespace OAI

universe uK

/-!
# Literal coefficients and actual symmetric multilinear forms

A coefficient is assigned freely to every multiset of basis indices, including
repetitions. Summing over ordered tuples gives an actual multilinear map. Basis
evaluation recovers every coefficient, and every permutation-invariant
multilinear map arises this way. The degree-zero case is included.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators

namespace SymmetricForm

variable {K : Type uK} [CommSemiring K] {r j : ℕ}

/-- Evaluation at the specified basis tuple recovers its literal coefficient. -/
theorem eval_basis (F : SymmetricForm K r j) (a : Fin j → Fin r) :
    eval F (fun i => Pi.single (a i) (1 : K)) = F (tupleSym a) := by
  classical
  unfold eval
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hba
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ a i :=
      not_forall.mp (fun h => hba (funext h))
    have hzero : (∏ i : Fin j, (Pi.single (a i) (1 : K) : Fin r → K) (b i)) =
        (0 : K) := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp [hi]
    rw [hzero, mul_zero]
  · intro h
    exact (h (Finset.mem_univ a)).elim

section Ring

variable {K : Type uK} [CommRing K] {r j : ℕ}

end Ring

end SymmetricForm

end MetricEntropyDuality

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.SymmetricForm
open scoped BigOperators


theorem solution.{uK} : type_of% @_root_.OAI.MetricEntropyDuality.SymmetricForm.eval_basis.{uK} := @_root_.OAI.MetricEntropyDuality.SymmetricForm.eval_basis.{uK}
