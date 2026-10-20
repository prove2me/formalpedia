-- Prove2me | solution 1 for OAI.MetricEntropyDuality.exists_prime_for_rank
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:37:01.007797+00:00
-- url     : https://prove2.me/submissions/fc07046f-8e5c-4bb6-8967-009118d9f856

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

open OAI OAI.MetricEntropyDuality


theorem solution {a : ℝ} (ha : 1 ≤ a) {r : ℕ} (hr : 0 < r)
    (B bound : ℝ) (hB : 0 < B) :
    let h := compressionRadius a
    let D := formDimension r h
    let u := directionCount r h (accuracy a)
    let C := encodingCost h (accuracy a) u
    ∃ p : ℕ, p.Prime ∧ bound < (p : ℝ) ∧ h < p ∧
      h ^ 2 * u ^ (2 * h) < p ∧ Real.exp (B * C / (D : ℝ)) < (p : ℝ) ∧
      0 < Real.log (p : ℝ) ∧ B * C < (D : ℝ) * Real.log (p : ℝ) ∧
      2 * C / ((D : ℝ) * Real.log (p : ℝ)) < 2 / B ∧ 0 < C := by
  intro h D u C
  have hθ : 0 < accuracy a := by unfold accuracy; positivity
  have hD : (1 : ℝ) ≤ D := by
    have h1 : 1 ≤ h := by
      show 1 ≤ compressionRadius a
      unfold compressionRadius; omega
    have : r ≤ formDimension r h := by
      unfold formDimension
      clear_value h
      induction h with
      | zero => omega
      | succ k ih =>
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · simp
        · have := ih hk
          have e : r + (k + 1) - 1 = (r + k - 1) + 1 := by omega
          rw [e, Nat.choose_succ_succ]
          omega
    have : 1 ≤ D := le_trans hr this
    exact_mod_cast this
  have hC : 0 < C := by
    show 0 < encodingCost h (accuracy a) u
    unfold encodingCost
    have hu : (0:ℝ) ≤ Real.log (u : ℝ) := Real.log_natCast_nonneg u
    have hh : (0:ℝ) < h := by
      show (0:ℝ) < (compressionRadius a : ℕ)
      unfold compressionRadius; positivity
    have hps : (0:ℝ) < pivotSlots (accuracy a) := by
      unfold pivotSlots
      have : (0:ℝ) < 1 / accuracy a := by positivity
      exact_mod_cast Nat.ceil_pos.mpr this
    have hlog : 0 < Real.log (1 + (pivotSlots (accuracy a) : ℝ) * (2 : ℝ) ^ u / accuracy a) := by
      apply Real.log_pos
      have : 0 < (pivotSlots (accuracy a) : ℝ) * (2 : ℝ) ^ u / accuracy a := by positivity
      linarith
    have := mul_pos (mul_pos (mul_pos hh hps) (by positivity : (0:ℝ) < (2:ℝ) ^ u)) hlog
    linarith
  obtain ⟨p, hp, hprime⟩ := Nat.exists_infinite_primes
    (max (max (⌈bound⌉₊ + 1) (h + 1)) (max (h ^ 2 * u ^ (2 * h) + 1) (⌈Real.exp (B * C / D)⌉₊ + 1)))
  simp only [max_le_iff] at hp
  obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
  have hpb : bound < (p : ℝ) := by
    have := Nat.le_ceil bound
    have : ((⌈bound⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp1
    push_cast at this; linarith
  have hpe : Real.exp (B * C / D) < (p : ℝ) := by
    have := Nat.le_ceil (Real.exp (B * C / D))
    have : ((⌈Real.exp (B * C / D)⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp4
    push_cast at this; linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hprime.one_lt)
  have hDpos : (0:ℝ) < D := by linarith
  have hBC : B * C < D * Real.log p := by
    have := Real.log_lt_log (Real.exp_pos _) hpe
    rw [Real.log_exp, div_lt_iff₀ hDpos] at this
    linarith
  refine ⟨p, hprime, hpb, by omega, by omega, hpe, hlogp, hBC, ?_, hC⟩
  rw [div_lt_div_iff₀ (by positivity) hB]
  nlinarith

