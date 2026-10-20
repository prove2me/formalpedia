-- Prove2me | solution 2 for OAI.MetricEntropyDuality.LogProfile.dilation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:05:51.056968+00:00
-- url     : https://prove2.me/submissions/598c3318-d277-4834-8ab2-f01651565b96

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/LogProfile.lean:L151-L185
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.LogProfile.dilation. The node keeps its source
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
import Definitions.Def_OAI_Analysis_MetricEntropy_PartitionGraph
import Definitions.Def_OAI_Analysis_MetricEntropy_FieldGraphSeparation
import Definitions.Def_OAI_Analysis_MetricEntropy_LogProfile
import Theorems.Thm_OAI_MetricEntropyDuality_LogProfile_phi_eq_sum

-- ---- from OAI.Analysis.MetricEntropy.LogProfile ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# The finite logarithmic profile

The profile is zero at infinite graph distance. Its exact finite expansion
and the factor-three dilation estimate include distances beyond the cutoff.
-/

noncomputable section

namespace MetricEntropyDuality.LogProfile

open scoped BigOperators

theorem log_cutoff_pos {h : ℕ} (hh : 0 < h) : 0 < Real.log ((h : ℝ) + 1) := by
  apply Real.log_pos
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  linarith

theorem phi_nonneg (h : ℕ) (d : ℕ∞) : 0 ≤ phi h d := by
  unfold phi
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

/-- The exact discrete factor-three dilation bound. -/
theorem dilation {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    (∑ j ∈ Finset.range h,
      if d ≤ ((3 * j + 2 : ℕ) : ℕ∞) then gamma h j else 0) ≤
      phi h d + Real.log 3 / Real.log ((h : ℝ) + 1) := by
  have hL := log_cutoff_pos hh
  have herror : 0 ≤ Real.log 3 / Real.log ((h : ℝ) + 1) :=
    div_nonneg (Real.log_nonneg (by norm_num)) hL.le
  cases d using ENat.recTopCoe with
  | top =>
      simpa only [phi_top, top_le_iff, ENat.natCast_ne_top, ite_false,
        Finset.sum_const_zero, zero_add] using herror
  | coe d =>
      have hsum : (∑ j ∈ Finset.range h,
          if (d : ℕ∞) ≤ ((3 * j + 2 : ℕ) : ℕ∞) then gamma h j else 0) =
          phi h ((d / 3 : ℕ) : ℕ∞) := by
        rw [phi_eq_sum hh]
        apply Finset.sum_congr rfl
        intro j _
        have hdj : d ≤ 3 * j + 2 ↔ d / 3 ≤ j := by omega
        simp only [ENat.natCast_le_natCast, hdj]
      rw [hsum, phi_coe]
      have hd : (d : ℝ) + 1 ≤ 3 * ((d / 3 : ℕ) + 1 : ℝ) := by
        have hdNat : d + 1 ≤ 3 * (d / 3 + 1) := by omega
        exact_mod_cast hdNat
      have hlog := Real.log_le_log (by positivity : 0 < (d : ℝ) + 1) hd
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity)] at hlog
      have hquot := div_le_div_of_nonneg_right hlog hL.le
      rw [add_div] at hquot
      have hbase : 1 - Real.log ((d : ℝ) + 1) / Real.log ((h : ℝ) + 1) ≤
          phi h (d : ℕ∞) := by
        rw [phi_coe]
        exact le_max_right _ _
      apply max_le (add_nonneg (phi_nonneg _ _) herror)
      linarith

end MetricEntropyDuality.LogProfile

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.LogProfile
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.LogProfile.dilation := @_root_.OAI.MetricEntropyDuality.LogProfile.dilation
