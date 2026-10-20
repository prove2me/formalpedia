-- Prove2me | solution 1 for OAI.MetricEntropyDuality.DirectionDeletion.exists_good_subset
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:35:56.063984+00:00
-- url     : https://prove2.me/submissions/68885735-ef93-4c07-930a-971145782051

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

open OAI OAI.MetricEntropyDuality
universe uU
open scoped Classical


theorem solution {U : Type uU} [Fintype U] {h w : ℕ}
    (bad : (Fin h → U) → Prop) (hh : 0 < h)
    (hno : ¬ ∃ L : Fin w → Fin h → U,
      (∀ i, bad (L i)) ∧ DisjointSupports L) :
    ∃ T : Finset U, (Finset.univ \ T).card ≤ h * (w - 1) ∧
      ∀ a : Fin h → U, (∀ j, a j ∈ T) → ¬bad a := by
  classical
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    exact absurd ⟨Fin.elim0, fun i => i.elim0, by intro i; exact i.elim0⟩ hno
  let P : ℕ → Prop := fun k => ∃ L : Fin k → Fin h → U, (∀ i, bad (L i)) ∧ DisjointSupports L
  have hPw : ¬ P w := hno
  have hex : ∃ k, ¬ P (k + 1) := ⟨w - 1, by rw [Nat.sub_add_cancel hw]; exact hPw⟩
  let k0 := Nat.find hex
  have hk0 : ¬ P (k0 + 1) := Nat.find_spec hex
  have hP0 : P k0 := by
    rcases Nat.eq_zero_or_pos k0 with h0 | h0
    · rw [h0]
      exact ⟨Fin.elim0, fun i => i.elim0, by intro i; exact i.elim0⟩
    · have hm : k0 - 1 < k0 := by omega
      have := Nat.find_min hex hm
      rw [not_not, Nat.sub_add_cancel h0] at this
      exact this
  have hk0w : k0 ≤ w - 1 := Nat.find_min' hex (by rw [Nat.sub_add_cancel hw]; exact hPw)
  obtain ⟨L, hLbad, hLdisj⟩ := hP0
  let S : Finset U := Finset.univ.biUnion (fun i => tupleSupport (L i))
  refine ⟨Finset.univ \ S, ?_, ?_⟩
  · rw [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)]
    calc S.card ≤ ∑ i, (tupleSupport (L i)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin k0, h := by
          refine Finset.sum_le_sum fun i _ => ?_
          unfold tupleSupport
          exact (Finset.card_image_le).trans (by simp)
      _ = k0 * h := by simp
      _ ≤ h * (w - 1) := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_left _ hk0w
  · intro a ha hbad
    apply hk0
    have haS : ∀ x ∈ tupleSupport a, x ∉ S := by
      intro x hx
      rw [mem_tupleSupport] at hx
      obtain ⟨j, rfl⟩ := hx
      have := ha j
      simp only [Finset.mem_sdiff] at this
      exact this.2
    have hLS : ∀ i, ∀ x ∈ tupleSupport (L i), x ∈ S := by
      intro i x hx
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hx⟩
    refine ⟨Fin.cons a L, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => simpa using hbad
      | succ i => simpa using hLbad i
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact Finset.disjoint_left.mpr fun x hx hx' => haS x hx (hLS j x hx')
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ]
          exact Finset.disjoint_right.mpr fun x hx hx' => haS x hx (hLS i x hx')
        | succ j =>
          simp only [Fin.cons_succ]
          exact hLdisj (fun e => hij (by rw [e]))

