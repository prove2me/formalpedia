-- Prove2me | solution 2 for OAI.MetricEntropyDuality.tupleSym_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:40:48.721394+00:00
-- url     : https://prove2.me/submissions/f89f7ab9-5315-49e6-baa1-75abcdde1d65

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/SymmetricIndex.lean:L57-L72
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.tupleSym_eq_iff. The node keeps its source
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

-- ---- from OAI.Analysis.MetricEntropy.SymmetricIndex ----
namespace OAI

/-!
# Symmetric indices of tuples

A tuple is sent to its literal multiset of entries. Repeated entries are retained.
Two tuples have the same index exactly when a permutation of their slots relates them.
-/

namespace MetricEntropyDuality

/-- A multiset count is the number of slots carrying that basis index. -/
theorem tupleSym_count {r j : ℕ} (a : Fin j → Fin r) (x : Fin r) :
    (tupleSym a : Multiset (Fin r)).count x = Fintype.card {i // a i = x} := by
  classical
  simpa only [coe_tupleSym, Multiset.coe_count, Fintype.card_subtype,
    List.Vector.get_ofFn, List.Vector.toList_ofFn] using
    (Fin.card_filter_univ_eq_vector_get_eq_count x (List.Vector.ofFn a)).symm

/-- Equality of indices is precisely permutation of tuple slots. -/
theorem tupleSym_eq_iff {r j : ℕ} (a b : Fin j → Fin r) :
    tupleSym a = tupleSym b ↔ ∃ σ : Equiv.Perm (Fin j), a ∘ σ = b := by
  classical
  constructor
  · intro h
    have hc (x : Fin r) : Fintype.card {i // b i = x} = Fintype.card {i // a i = x} := by
      simpa only [tupleSym_count] using
        congrArg (fun s : Sym (Fin r) j => (s : Multiset (Fin r)).count x) h.symm
    let es : ∀ x : Fin r, {i // b i = x} ≃ {i // a i = x} :=
      fun x => Fintype.equivOfCardEq (hc x)
    refine ⟨Equiv.ofFiberEquiv es, ?_⟩
    funext i
    exact Equiv.ofFiberEquiv_map es i
  · rintro ⟨σ, rfl⟩
    exact (tupleSym_comp_perm a σ).symm

end MetricEntropyDuality

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.tupleSym_eq_iff := @_root_.OAI.MetricEntropyDuality.tupleSym_eq_iff
