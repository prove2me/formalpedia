-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.FiniteLaw.exists_le_expectation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:47:39.976337+00:00
-- url     : https://prove2.me/submissions/55f78a3c-e18b-445e-a681-341e8a52a33e

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/ProbabilisticExistence.lean:L31-L45
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.FiniteLaw.exists_le_expectation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringSampledFamilies
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bernoulli
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringResidualTuples
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringNumericalBounds

-- ---- from OAI.Combinatorics.DiscreteConvexity.ProbabilisticExistence ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Extracting outcomes from a finite probability law

Normalization guarantees a positive-weight outcome. It also guarantees an
outcome below the expectation and a witness to every positive-probability
event; strict positivity of every individual mass is not required.
-/

namespace TalagrandDiscreteConvexity.FiniteLaw

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω]

theorem exists_weight_pos (μ : FiniteLaw Ω) : ∃ ω, 0 < μ.weight ω := by
  classical
  by_contra h
  have hz (ω : Ω) : μ.weight ω = 0 :=
    le_antisymm (le_of_not_gt (fun hp => h ⟨ω, hp⟩)) (μ.nonneg ω)
  have htotal : (∑ ω, μ.weight ω) = 0 := by simp [hz]
  rw [μ.total] at htotal
  exact one_ne_zero htotal

theorem exists_le_expectation (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    ∃ ω, f ω ≤ μ.expectation f := by
  classical
  obtain ⟨ω₀, hω₀⟩ := μ.exists_weight_pos
  by_contra h
  have hlt (ω : Ω) : μ.expectation f < f ω :=
    lt_of_not_ge (fun hle => h ⟨ω, hle⟩)
  have hsum : μ.expectation (fun _ => μ.expectation f) < μ.expectation f := by
    apply Finset.sum_lt_sum
    · intro ω _
      exact mul_le_mul_of_nonneg_left (hlt ω).le (μ.nonneg ω)
    · exact ⟨ω₀, Finset.mem_univ ω₀,
        mul_lt_mul_of_pos_left (hlt ω₀) hω₀⟩
  rw [expectation_const] at hsum
  exact (lt_irrefl _) hsum

end TalagrandDiscreteConvexity.FiniteLaw

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.FiniteLaw
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.exists_le_expectation := @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.exists_le_expectation
