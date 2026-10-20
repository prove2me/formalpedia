-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_eq_mass
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T16:58:29.226802+00:00
-- url     : https://prove2.me/submissions/cfb6dbae-0cf9-4987-aedd-cdac67415031

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoordinateObservations.lean:L21-L47
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_eq_mass. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FourierWeights
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_SignedArrays
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_ProductProbability
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_FiniteLaw_prob_pi

-- ---- from OAI.Combinatorics.DiscreteConvexity.Bernoulli ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Bernoulli product laws and Boolean cubes

The algebraic identities hold for every real parameter. Nonnegative normalized
laws additionally require a parameter in the closed unit interval.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem bernoulliWeight_eq_mass (p : ℝ) (s : Finset α) :
    bernoulliWeight p s = bernoulliMass p s := by
  simp only [bernoulliWeight, bernoulliMass, Finset.prod_ite,
    Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, Finset.prod_const]

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.CoordinateObservations ----
namespace OAI

/-!
# Boolean observations of finite product laws

Independent Boolean observations with common success probability have the
Bernoulli law on subsets, both on individual atoms and on arbitrary families.
-/

open scoped BigOperators
noncomputable section

namespace TalagrandDiscreteConvexity

variable {α : Type*} [Fintype α] [DecidableEq α]
  {Ω : α → Type*} [∀ i, Fintype (Ω i)]

/-- A specified set of successful coordinate observations has its Bernoulli mass. -/
theorem prob_pi_cubeSet_eq_mass (μ : ∀ i, FiniteLaw (Ω i))
    (obs : ∀ i, Ω i → Bool) (p : ℝ)
    (hobs : ∀ i, (μ i).prob (fun w => obs i w = true) = p) (s : Finset α) :
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) = s) =
      bernoulliMass p s := by
  classical
  have hcoord (i : α) :
      (μ i).prob (fun w => (obs i w = true ↔ i ∈ s)) =
        if i ∈ s then p else 1 - p := by
    by_cases hi : i ∈ s
    · simpa [hi] using hobs i
    · simpa [hi, hobs i] using (μ i).prob_compl (fun w => obs i w = true)
  calc
    (FiniteLaw.pi μ).prob (fun ω => cubeSet (fun i => obs i (ω i)) = s) =
        (FiniteLaw.pi μ).prob (fun ω => ∀ i, obs i (ω i) = true ↔ i ∈ s) := by
      congr 1
      funext ω
      apply propext
      simp only [Finset.ext_iff, mem_cubeSet]
    _ = ∏ i, (μ i).prob (fun w => (obs i w = true ↔ i ∈ s)) :=
      FiniteLaw.prob_pi μ (fun i w => (obs i w = true ↔ i ∈ s))
    _ = ∏ i, if i ∈ s then p else 1 - p := by
      apply Finset.prod_congr rfl
      intro i _
      exact hcoord i
    _ = bernoulliMass p s := bernoulliWeight_eq_mass p s

end TalagrandDiscreteConvexity

end

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_eq_mass := @_root_.OAI.TalagrandDiscreteConvexity.prob_pi_cubeSet_eq_mass
