-- Prove2me | solution 2 for OAI.MetricEntropyDuality.ProfileMixtures.dilated_level_sum_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:16:03.474539+00:00
-- url     : https://prove2.me/submissions/df97daa3-af29-405d-afa4-108bde0fc1d2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/MetricEntropy/ProfileMixtures.lean:L82-L113
-- (upload_full_project.md Phase 4): solution for node OAI.MetricEntropyDuality.ProfileMixtures.dilated_level_sum_le. The node keeps its source
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
import Definitions.Def_OAI_Analysis_MetricEntropy_GraphProfile
import Definitions.Def_OAI_Analysis_MetricEntropy_FiniteFieldRows
import Definitions.Def_OAI_Analysis_MetricEntropy_GreedyPivots
import Definitions.Def_OAI_Analysis_MetricEntropy_CompressionLevels
import Definitions.Def_OAI_Analysis_MetricEntropy_ProfileMixtures
import Theorems.Thm_OAI_MetricEntropyDuality_LogProfile_dilation

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

theorem dilation_mul_indicator {h : ℕ} (hh : 0 < h) (d : ℕ∞) :
    (∑ j ∈ Finset.range h,
      gamma h j * (if d ≤ ((3 * j + 2 : ℕ) : ℕ∞) then (1 : ℝ) else 0)) ≤
      phi h d + Real.log 3 / Real.log ((h : ℝ) + 1) := by
  simpa only [mul_ite, mul_one, mul_zero] using dilation hh d

end MetricEntropyDuality.LogProfile

end

end OAI

-- ---- from OAI.Analysis.MetricEntropy.ProfileMixtures ----
namespace OAI

universe uX uY uι uLabel uJ

/-!
# Combining graph-ball levels using the actual logarithmic profile

The profile expansion and dilation estimate are applied to each actual extended
graph distance. The finite sums below retain disconnected distances, with no
extra finite-distance hypothesis. The final theorem combines the two losses
from column assignment and the one loss from rounding.
-/

noncomputable section

namespace MetricEntropyDuality.ProfileMixtures

open scoped BigOperators

variable {X : Type uX} {Y : Type uY} {ι : Type uι} {Label : ι → Type uLabel} [Fintype Y]

private theorem ballIndicator_eq_distance (L : (i : ι) → X → Label i)
    (T : Finset ι) (j : ℕ) (x v : X) :
    CompressionLevels.ballIndicator L T j x v =
      if PartitionGraph.distance L T x v ≤ (j : ℕ∞) then (1 : ℝ) else 0 := by
  by_cases hd : PartitionGraph.distance L T x v ≤ (j : ℕ∞)
  · simp [CompressionLevels.ballIndicator, PartitionGraph.near, hd]
  · simp [CompressionLevels.ballIndicator, PartitionGraph.near, hd]

private theorem sum_weighted_levels {J : Type uJ} [Fintype J]
    (α : J → ℝ) (μ : Y → ℝ) (b : J → Y → ℝ) :
    (∑ j, α j * ∑ y, μ y * b j y) =
      ∑ y, μ y * ∑ j, α j * b j y := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual factor-three dilation bound survives mixing columns whose
nonnegative coefficients have total mass at most one. -/
theorem dilated_level_sum_le (L : (i : ι) → X → Label i) (v : Y → X)
    (T : Y → Finset ι) (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y)
    (hmass : ∑ y, μ y ≤ 1) {h : ℕ} (hh : 0 < h) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hprofile : Real.log 3 / Real.log ((h : ℝ) + 1) ≤ θ) (x : X) :
    (∑ j : Fin h, LogProfile.gamma h j.val *
      CompressionLevels.levelValue L v T μ (3 * j.val + 2) x) ≤
        profileMixture L v T h μ x + θ := by
  unfold CompressionLevels.levelValue
  rw [sum_weighted_levels]
  calc
    (∑ y, μ y * ∑ j : Fin h, LogProfile.gamma h j.val *
        CompressionLevels.ballIndicator L (T y) (3 * j.val + 2) x (v y)) ≤
        ∑ y, μ y * (LogProfile.phi h (PartitionGraph.distance L (T y) x (v y)) + θ) := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (hμ y)
      have hd : (∑ j : Fin h, LogProfile.gamma h j.val *
          CompressionLevels.ballIndicator L (T y) (3 * j.val + 2) x (v y)) ≤
            LogProfile.phi h (PartitionGraph.distance L (T y) x (v y)) +
              Real.log 3 / Real.log ((h : ℝ) + 1) := by
        rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => LogProfile.gamma h j *
          CompressionLevels.ballIndicator L (T y) (3 * j + 2) x (v y)) h]
        simpa only [ballIndicator_eq_distance] using
          LogProfile.dilation_mul_indicator hh (PartitionGraph.distance L (T y) x (v y))
      exact hd.trans (add_le_add (le_refl _) hprofile)
    _ = profileMixture L v T h μ x + (∑ y, μ y) * θ := by
      simp only [profileMixture, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ profileMixture L v T h μ x + θ := by
      apply add_le_add (le_refl _)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hθ0

end MetricEntropyDuality.ProfileMixtures

end

end OAI

-- ---- platform node ----
open OAI OAI.MetricEntropyDuality OAI.MetricEntropyDuality.ProfileMixtures
open scoped BigOperators


theorem solution.{uX,uY,uι,uLabel} : type_of% @_root_.OAI.MetricEntropyDuality.ProfileMixtures.dilated_level_sum_le.{uX,uY,uι,uLabel} := @_root_.OAI.MetricEntropyDuality.ProfileMixtures.dilated_level_sum_le.{uX,uY,uι,uLabel}
