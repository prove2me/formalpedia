-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_exists_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:00:06.273299+00:00
-- url     : https://prove2.me/submissions/c28f5e32-2c3e-4c26-9c4f-e8b0c6e5a337

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/UnionBound.lean:L14-L39
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_exists_le. The node keeps its source
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

-- ---- from OAI.Combinatorics.DiscreteConvexity.FiniteProbability ----
namespace OAI

/-!
# Finite probability laws

All probabilities and expectations are finite real sums. Finite laws admit
elementary probability inequalities, product laws, independent samples, and
uniform distributions.
-/

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

namespace TalagrandDiscreteConvexity

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_sum {ι : Type*} [Fintype ι] (μ : FiniteLaw Ω) (f : ι → Ω → ℝ) :
    μ.expectation (fun ω => ∑ i, f i ω) = ∑ i, μ.expectation (f i) := by
  simp only [expectation, Finset.mul_sum]
  exact Finset.sum_comm

theorem expectation_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (hfg : ∀ ω, f ω ≤ g ω) :
    μ.expectation f ≤ μ.expectation g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (hfg ω) (μ.nonneg ω)

theorem prob_eq_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) :
    μ.prob P = μ.expectation (fun ω => if P ω then 1 else 0) := by
  classical
  simp [prob, expectation, mul_ite]

theorem prob_le_expectation (μ : FiniteLaw Ω) (P : Ω → Prop) (f : Ω → ℝ)
    (hf : ∀ ω, 0 ≤ f ω) (hP : ∀ ω, P ω → 1 ≤ f ω) : μ.prob P ≤ μ.expectation f := by
  classical
  rw [prob_eq_expectation]
  apply μ.expectation_mono
  intro ω
  by_cases hp : P ω
  · simpa [hp] using hP ω hp
  · simpa [hp] using hf ω

end FiniteLaw

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.UnionBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity.FiniteLaw

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- The indexed union bound uses no independence among the events. -/
theorem prob_exists_le (μ : FiniteLaw Ω) (P : ι → Ω → Prop) :
    μ.prob (fun ω => ∃ i, P i ω) ≤ ∑ i, μ.prob (P i) := by
  classical
  calc
    μ.prob (fun ω => ∃ i, P i ω) ≤
        μ.expectation (fun ω => ∑ i, if P i ω then (1 : ℝ) else 0) := by
      apply μ.prob_le_expectation
      · intro ω
        exact Finset.sum_nonneg fun i _ => by
          by_cases h : P i ω <;> simp [h]
      · intro ω hω
        obtain ⟨i, hi⟩ := hω
        have hsum : (if P i ω then (1 : ℝ) else 0) ≤
            ∑ j, if P j ω then (1 : ℝ) else 0 := by
          apply Finset.single_le_sum (a := i)
            (f := fun j => if P j ω then (1 : ℝ) else 0)
          · intro j _
            by_cases h : P j ω <;> simp [h]
          · exact Finset.mem_univ i
        simpa only [ite_eq_left hi] using hsum
    _ = ∑ i, μ.prob (P i) := by
      rw [μ.expectation_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact (μ.prob_eq_expectation (P i)).symm

end TalagrandDiscreteConvexity.FiniteLaw

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity OAI.TalagrandDiscreteConvexity.FiniteLaw
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_exists_le := @_root_.OAI.TalagrandDiscreteConvexity.FiniteLaw.prob_exists_le
