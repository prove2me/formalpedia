-- Prove2me | solution 2 for OAI.MetricEntropyDuality.LogProfile.phi_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:04:56.213351+00:00
-- url     : https://prove2.me/submissions/6241a10e-3272-42ed-aea4-a5bc7a376333

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/LogProfile.lean:L122-L140
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.LogProfile.phi_eq_sum. The node keeps its source
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
import Theorems.Thm_OAI_MetricEntropyDuality_LogProfile_phi_eq_zero_of_le
import Theorems.Thm_OAI_MetricEntropyDuality_LogProfile_sum_log_steps

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

private theorem sum_gamma_tail (h d : ℕ) :
    (∑ j ∈ Finset.range h, if d ≤ j then gamma h j else 0) =
      (Real.log ((h : ℝ) + 1) - Real.log (((min d h : ℕ) : ℝ) + 1)) /
        Real.log ((h : ℝ) + 1) := by
  calc
    _ = (∑ j ∈ Finset.range h,
        if d ≤ j then Real.log ((j : ℝ) + 2) - Real.log ((j : ℝ) + 1) else 0) /
          Real.log ((h : ℝ) + 1) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hd : d ≤ j <;> simp [hd, gamma]
    _ = _ := by rw [sum_log_steps]

/-- Exact expansion into the finite graph-ball indicators. -/
theorem phi_eq_sum {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    phi h d = ∑ j ∈ Finset.range h, if d ≤ (j : ℕ∞) then gamma h j else 0 := by
  cases d using ENat.recTopCoe with
  | top => simp
  | coe d =>
      simp only [ENat.natCast_le_natCast]
      rw [sum_gamma_tail]
      by_cases hd : d ≤ h
      · have hlog : Real.log ((d : ℝ) + 1) ≤ Real.log ((h : ℝ) + 1) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast Nat.add_le_add_right hd 1
        have hratio : Real.log ((d : ℝ) + 1) / Real.log ((h : ℝ) + 1) ≤ 1 :=
          (div_le_one (log_cutoff_pos hh)).2 hlog
        rw [phi_coe, min_eq_left hd, sub_div, div_self (log_cutoff_pos hh).ne',
          max_eq_right (sub_nonneg.mpr hratio)]
      · have hhd : h ≤ d := by omega
        rw [phi_eq_zero_of_le hh (ENat.natCast_le_natCast.mpr hhd), min_eq_right hhd,
          sub_self, zero_div]

end MetricEntropyDuality.LogProfile

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.LogProfile
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.MetricEntropyDuality.LogProfile.phi_eq_sum := @_root_.OAI.MetricEntropyDuality.LogProfile.phi_eq_sum
