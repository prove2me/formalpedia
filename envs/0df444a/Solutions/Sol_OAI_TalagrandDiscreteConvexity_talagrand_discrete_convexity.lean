-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:04:20.760657+00:00
-- url     : https://prove2.me/submissions/31a3d47e-284e-4dc1-b97b-9b7f464b8afb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/Main.lean:L61-L65
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_TalagrandDiscreteConvexity_talagrand_discrete_convexity) verbatim and is proved by it.
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_SignedArrays
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_ProductProbability
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_LabelCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_MandatoryCoupling
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_UnionTuples
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_original_density_small

-- ---- from OAI.Combinatorics.DiscreteConvexity.Main ----
namespace OAI

/-!
# Talagrand discrete convexity at the original density

Independent coordinate choices produce dependent rows with full Bernoulli
subset laws. The label construction raises the union density when `L p < 1`;
the mandatory-row construction covers every coordinate when `1 ≤ L p`.
Both cases use the same row-failure budget, without independence between rows.
-/

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem talagrand_discrete_convexity (N : ℕ) (_hN : 1 ≤ N)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (D : Family (Fin N))
    (hD : 1 - 1 / (2 : ℝ) ^ 75 ≤ familyMeasure p D) :
    Small p (exceptional ((2 : ℕ) ^ 75) D) :=
  original_density_small p hp0 hp1 D hD

end TalagrandDiscreteConvexity

end OAI

-- ---- mission target ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

namespace OAI
namespace TalagrandDiscreteConvexity
theorem _root_.solution (N : ℕ) (_hN : 1 ≤ N)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (D : Family (Fin N))
    (hD : 1 - 1 / (2 : ℝ) ^ 75 ≤ familyMeasure p D) :
    Small p (exceptional ((2 : ℕ) ^ 75) D) := by
  first
    | exact OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity N _hN p hp0 hp1 D hD
    | exact OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity
    | (apply OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity <;> assumption)
    | (intros; apply OAI.TalagrandDiscreteConvexity.talagrand_discrete_convexity <;> assumption)
end TalagrandDiscreteConvexity
end OAI
