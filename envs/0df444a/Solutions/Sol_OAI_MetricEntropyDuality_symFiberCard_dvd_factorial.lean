-- Prove2me | solution 1 for OAI.MetricEntropyDuality.symFiberCard_dvd_factorial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:32:28.683086+00:00
-- url     : https://prove2.me/submissions/f97c4de1-58fc-4e05-b1cd-99ded1e3424e

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

open OAI OAI.MetricEntropyDuality
lemma h51m_tse {r j : ℕ} (a b : Fin j → Fin r) :
    tupleSym a = tupleSym b ↔ ∃ σ : Equiv.Perm (Fin j), a ∘ σ = b := by
  constructor
  · intro h
    have hp : List.Perm (List.ofFn a) (List.ofFn b) := by
      have := congrArg (fun s : Sym (Fin r) j => (s : Multiset (Fin r))) h
      simpa [coe_tupleSym] using this
    have h1 := Tuple.monotone_sort a
    have h2 := Tuple.monotone_sort b
    have hp2 : List.Perm (List.ofFn (a ∘ Tuple.sort a)) (List.ofFn (b ∘ Tuple.sort b)) :=
      ((Tuple.sort a).ofFn_comp_perm a).trans (hp.trans ((Tuple.sort b).ofFn_comp_perm b).symm)
    have heq : a ∘ Tuple.sort a = b ∘ Tuple.sort b :=
      List.ofFn_injective (hp2.eq_of_pairwise' h1.sortedLE_ofFn.pairwise h2.sortedLE_ofFn.pairwise)
    refine ⟨Tuple.sort a * (Tuple.sort b)⁻¹, ?_⟩
    funext i
    have := congrFun heq ((Tuple.sort b)⁻¹ i)
    simpa [Equiv.Perm.mul_apply] using this
  · rintro ⟨σ, rfl⟩
    exact (tupleSym_comp_perm a σ).symm

theorem solution {r j : ℕ} (s : Sym (Fin r) j) :
    symFiberCard s ∣ j.factorial := by
  classical
  -- a representative tuple
  set l := (s : Multiset (Fin r)).toList with hl
  have hlen : l.length = j := by rw [hl, Multiset.length_toList]; exact s.2
  let a0 : Fin j → Fin r := fun i => l.get ⟨i, by omega⟩
  have ha0 : tupleSym a0 = s := by
    apply Sym.ext
    rw [coe_tupleSym]
    have : List.ofFn a0 = l := by
      apply List.ext_get (by simp [hlen])
      intro n h1 h2; simp [a0]
    rw [this, hl, Multiset.coe_toList]
  letI : MulAction (Equiv.Perm (Fin j)) (Fin j → Fin r) := arrowAction
  have hiff : ∀ a : Fin j → Fin r, tupleSym a = s ↔ a ∈ MulAction.orbit (Equiv.Perm (Fin j)) a0 := by
    intro a
    rw [MulAction.mem_orbit_iff, ← ha0, eq_comm, h51m_tse]
    constructor
    · rintro ⟨σ, hσ⟩
      exact ⟨σ⁻¹, by rw [← hσ]; funext i; rfl⟩
    · rintro ⟨g, hg⟩
      exact ⟨g⁻¹, by rw [← hg]; funext i; rfl⟩
  unfold symFiberCard
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff)]
  have := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Equiv.Perm (Fin j)) a0
  rw [Fintype.card_perm, Fintype.card_fin] at this
  exact Dvd.intro _ this

