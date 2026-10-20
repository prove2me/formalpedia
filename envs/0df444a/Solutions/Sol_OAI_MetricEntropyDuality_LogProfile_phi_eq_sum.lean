-- Prove2me | solution 1 for OAI.MetricEntropyDuality.LogProfile.phi_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:53:07.029612+00:00
-- url     : https://prove2.me/submissions/5f923116-7dd1-422e-8550-de162e98b76f

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
import Definitions.Def_OAI_Analysis_MetricEntropy_FormContraction
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile

open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.LogProfile
open scoped BigOperators
theorem h51b_tele (n : ℕ) : ∀ m : ℕ, (∑ j ∈ Finset.range m,
    if n ≤ j then (Real.log ((j:ℝ) + 2) - Real.log ((j:ℝ) + 1)) else 0) =
      if n ≤ m then Real.log ((m:ℝ) + 1) - Real.log ((n:ℝ) + 1) else 0
  | 0 => by
    by_cases h : n ≤ 0
    · have : n = 0 := by omega
      subst this
      simp
    · simp [h]
  | m + 1 => by
    rw [Finset.sum_range_succ, h51b_tele n m]
    by_cases h1 : n ≤ m
    · rw [if_pos h1, if_pos h1, if_pos (by omega)]
      push_cast
      ring
    · rw [if_neg h1, if_neg h1]
      by_cases h2 : n = m + 1
      · subst h2
        simp
      · rw [if_neg (by omega)]
        simp

theorem solution {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    phi h d = ∑ j ∈ Finset.range h, if d ≤ (j : ℕ∞) then gamma h j else 0 := by
  have hL : 0 < Real.log ((h : ℝ) + 1) := Real.log_pos (by
    have : (1:ℝ) ≤ h := by exact_mod_cast hh
    linarith)
  induction d using ENat.recTopCoe with
  | top => simp
  | coe n =>
    rw [phi_coe]
    have hterm : ∀ j ∈ Finset.range h, (if (n : ℕ∞) ≤ (j : ℕ∞) then gamma h j else 0) =
        (if n ≤ j then (Real.log ((j:ℝ) + 2) - Real.log ((j:ℝ) + 1)) else 0) /
          Real.log ((h : ℝ) + 1) := by
      intro j _
      by_cases hj : n ≤ j <;> simp [hj, gamma]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, h51b_tele]
    by_cases hnh : n ≤ h
    · rw [if_pos hnh]
      have hle : Real.log ((n:ℝ) + 1) ≤ Real.log ((h:ℝ) + 1) := by
        apply Real.log_le_log (by positivity)
        have : (n:ℝ) ≤ h := by exact_mod_cast hnh
        linarith
      rw [max_eq_right]
      · field_simp
      · rw [sub_nonneg, div_le_one hL]
        exact hle
    · rw [if_neg hnh, zero_div]
      apply max_eq_left
      rw [sub_nonpos, le_div_iff₀ hL, one_mul]
      apply Real.log_le_log (by positivity)
      have : (h:ℝ) ≤ n := by exact_mod_cast (le_of_lt (not_le.mp hnh))
      linarith

