-- Prove2me | solution 1 for OAI.MetricEntropyDuality.form_entropy_ratio_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:38:26.25019+00:00
-- url     : https://prove2.me/submissions/ba663b27-90f6-4b2a-94b0-e011a95cf083

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

open OAI OAI.MetricEntropyDuality
universe uα


theorem solution {r h s p Q : ℕ} {C : ℝ}
    (hr : 0 < r) (hh : 0 < h) (hp : 1 < p)
    (hQ : Real.log (Q : ℝ) ≤ (h : ℝ) * (s : ℝ) *
      Real.log ((p : ℝ) ^ formDimension r (h - 1)) + C) :
    Real.log ((Q : ℝ) ^ 2) / Real.log ((p : ℝ) ^ formDimension r h) ≤
      2 * (h : ℝ) ^ 2 * (s : ℝ) / ((r : ℝ) + h - 1) +
        2 * C / ((formDimension r h : ℝ) * Real.log (p : ℝ)) := by
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  have hkey : ((q + k + 1 : ℕ) : ℝ) * (formDimension (q+1) (k + 1 - 1) : ℝ) =
      (formDimension (q+1) (k+1) : ℝ) * ((k + 1 : ℕ) : ℝ) := by
    unfold formDimension
    have e1 : q + 1 + (k + 1 - 1) - 1 = q + k := by omega
    have e2 : q + 1 + (k + 1) - 1 = q + k + 1 := by omega
    rw [e1, e2, show k + 1 - 1 = k by omega]
    have := Nat.add_one_mul_choose_eq (q + k) k
    exact_mod_cast this
  set D' := (formDimension (q+1) (k + 1 - 1) : ℝ) with hD'
  set D := (formDimension (q+1) (k+1) : ℝ) with hD
  have hDpos : 0 < D := by
    rw [hD]; unfold formDimension
    exact_mod_cast Nat.choose_pos (by omega)
  have hL : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp)
  rw [Real.log_pow, Real.log_pow, ← hD]
  rw [Real.log_pow, ← hD'] at hQ
  have hrk : ((q + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) - 1 = ((q + k + 1 : ℕ) : ℝ) := by
    push_cast; ring
  rw [hrk]
  have hrkpos : (0 : ℝ) < ((q + k + 1 : ℕ) : ℝ) := by positivity
  have hD'eq : D' = D * ((k + 1 : ℕ) : ℝ) / ((q + k + 1 : ℕ) : ℝ) := by
    rw [eq_div_iff hrkpos.ne', mul_comm, hkey]
  rw [div_le_iff₀ (by positivity)]
  have expand : (2 * ((k + 1 : ℕ) : ℝ) ^ 2 * (s : ℝ) / ((q + k + 1 : ℕ) : ℝ) +
      2 * C / (D * Real.log p)) * (D * Real.log p) =
      2 * ((k + 1 : ℕ) : ℝ) * (s : ℝ) * (D' * Real.log p) + 2 * C := by
    rw [hD'eq]
    field_simp
  rw [expand]
  push_cast at hQ ⊢
  nlinarith

