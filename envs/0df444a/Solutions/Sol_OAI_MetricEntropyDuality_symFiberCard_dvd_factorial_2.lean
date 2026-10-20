-- Prove2me | solution 2 for OAI.MetricEntropyDuality.symFiberCard_dvd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:53:00.060019+00:00
-- url     : https://prove2.me/submissions/ddafdab5-0e4f-4687-8be3-3aee8c26cdea

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/SymmetricMultiplicity.lean:L28-L50
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.symFiberCard_dvd_factorial. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_tupleSym_eq_iff

-- ---- from OAI.Analysis.MetricEntropy.SymmetricIndex ----
namespace OAI

/-!
# Symmetric indices of tuples

A tuple is sent to its literal multiset of entries. Repeated entries are retained.
Two tuples have the same index exactly when a permutation of their slots relates them.
-/

namespace MetricEntropyDuality

/-- Every multiset of the prescribed size is represented by a tuple. -/
theorem tupleSym_surjective (r j : ℕ) : Function.Surjective (@tupleSym r j) := by
  induction j with
  | zero =>
      intro s
      exact ⟨Fin.elim0, Subsingleton.elim _ _⟩
  | succ j ih =>
      intro s
      rcases Sym.exists_eq_cons_of_succ s with ⟨a, t, rfl⟩
      obtain ⟨args, rfl⟩ := ih t
      exact ⟨Fin.cons a args, tupleSym_cons a args⟩

end MetricEntropyDuality

end OAI

-- ---- from OAI.Analysis.MetricEntropy.SymmetricMultiplicity ----
namespace OAI

/-!
# Multiplicities of symmetric indices

The tuples representing a fixed multiset form a permutation orbit. Its size is
positive and divides the factorial of the number of slots. Consequently the
coefficient multiplicity cannot vanish modulo a prime larger than that number.
-/

namespace MetricEntropyDuality

/-- The actual tuple fiber is a permutation orbit, so its size divides `j!`. -/
theorem symFiberCard_dvd_factorial {r j : ℕ} (s : Sym (Fin r) j) :
    symFiberCard s ∣ j.factorial := by
  classical
  obtain ⟨a, rfl⟩ := tupleSym_surjective r j s
  let G := DomMulAct (Equiv.Perm (Fin j))
  let : Fintype G := Fintype.ofEquiv (Equiv.Perm (Fin j)) DomMulAct.mk
  let eOrbit : {b : Fin j → Fin r // tupleSym b = tupleSym a} ≃ MulAction.orbit G a :=
    Equiv.subtypeEquivRight fun b => by
      rw [eq_comm, tupleSym_eq_iff, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨σ, hσ⟩
        exact ⟨DomMulAct.mk σ, hσ⟩
      · rintro ⟨σ, hσ⟩
        exact ⟨DomMulAct.mk.symm σ, hσ⟩
  have hg : Fintype.card G = j.factorial := by
    calc
      Fintype.card G = Fintype.card (Equiv.Perm (Fin j)) :=
        Fintype.card_congr DomMulAct.mk.symm
      _ = j.factorial := by rw [Fintype.card_perm, Fintype.card_fin]
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group G a
  rw [← Fintype.card_congr eOrbit, hg] at h
  exact ⟨Fintype.card (MulAction.stabilizer G a), h.symm⟩

end MetricEntropyDuality

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.symFiberCard_dvd_factorial := @_root_.OAI.MetricEntropyDuality.symFiberCard_dvd_factorial
