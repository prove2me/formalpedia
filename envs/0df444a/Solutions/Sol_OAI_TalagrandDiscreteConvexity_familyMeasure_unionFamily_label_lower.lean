-- Prove2me | solution 1 for OAI.TalagrandDiscreteConvexity.familyMeasure_unionFamily_label_lower
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T17:01:07.12909+00:00
-- url     : https://prove2.me/submissions/6ad3cba4-c09c-4938-80aa-9bcb0d3437d9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/LabelCoupling.lean:L152-L168
-- (upload_full_project.md Phase 4): solution for node OAI.TalagrandDiscreteConvexity.familyMeasure_unionFamily_label_lower. The node keeps its source
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
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_LabelCoupling
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_FiniteLaw_prob_exists_le
import Theorems.Thm_OAI_TalagrandDiscreteConvexity_prob_pi_cubeSet_mem_family

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

theorem prob_mono (μ : FiniteLaw Ω) {P Q : Ω → Prop} (hPQ : ∀ ω, P ω → Q ω) :
    μ.prob P ≤ μ.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : P ω
  · simp [hp, hPQ ω hp]
  · by_cases hq : Q ω <;> simp [hp, hq, μ.nonneg ω]

end FiniteLaw

end TalagrandDiscreteConvexity

end

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.UnionBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open scoped BigOperators

namespace TalagrandDiscreteConvexity.FiniteLaw

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- Simultaneous success is bounded using only the individual marginals. -/
theorem prob_forall_ge (μ : FiniteLaw Ω) (P : ι → Ω → Prop) :
    1 - ∑ i, (1 - μ.prob (P i)) ≤ μ.prob (fun ω => ∀ i, P i ω) := by
  classical
  have hbad := prob_exists_le μ (fun i ω => ¬ P i ω)
  have hcompl : μ.prob (fun ω => ¬ ∀ i, P i ω) ≤
      ∑ i, μ.prob (fun ω => ¬ P i ω) := by
    simpa only [not_forall] using hbad
  rw [μ.prob_compl] at hcompl
  simp_rw [μ.prob_compl] at hcompl
  linarith

theorem prob_forall_ge_of_const (μ : FiniteLaw Ω) (P : ι → Ω → Prop)
    (a : ℝ) (hmarginal : ∀ i, μ.prob (P i) = a) :
    1 - (Fintype.card ι : ℝ) * (1 - a) ≤ μ.prob (fun ω => ∀ i, P i ω) := by
  have h := prob_forall_ge μ P
  simpa only [hmarginal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

end TalagrandDiscreteConvexity.FiniteLaw

end OAI

-- ---- from OAI.Combinatorics.DiscreteConvexity.LabelCoupling ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TalagrandDiscreteConvexity

open scoped BigOperators

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem labelUnion_eq_cubeSet_nonzero {L : ℕ} (ω : α → Fin (L + 1)) :
    unionTuple (labelRow ω) = cubeSet (fun i => decide (ω i ≠ 0)) := by
  classical
  ext i
  simp only [mem_unionTuple, mem_labelRow, mem_cubeSet, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj⟩
    rw [hj]
    exact Fin.succ_ne_zero j
  · intro hi
    exact Fin.eq_succ_of_ne_zero hi

theorem labelRow_prob_mem_family (L : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hLp : (L : ℝ) * p ≤ 1) (j : Fin L) (D : Family α) :
    (labelSamples L p hp hLp).prob (fun ω => labelRow ω j ∈ D) =
      familyMeasure p D := by
  classical
  have hobs (i : α) :
      (labelLaw L p hp hLp).prob (fun k => decide (k = j.succ) = true) = p := by
    simpa only [decide_eq_true_eq] using labelLaw_prob_succ L p hp hLp j
  simpa only [labelSamples, labelRow] using
    prob_pi_cubeSet_mem_family (fun _ : α => labelLaw L p hp hLp)
      (fun _ k => decide (k = j.succ)) p hobs D

theorem labelUnion_prob_mem_family (L : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hLp : (L : ℝ) * p ≤ 1) (D : Family α) :
    (labelSamples L p hp hLp).prob (fun ω => unionTuple (labelRow ω) ∈ D) =
      familyMeasure ((L : ℝ) * p) D := by
  classical
  have hobs (i : α) :
      (labelLaw L p hp hLp).prob (fun k => decide (k ≠ 0) = true) = (L : ℝ) * p := by
    simpa only [decide_eq_true_eq] using labelLaw_prob_nonzero L p hp hLp
  simpa only [labelSamples, labelUnion_eq_cubeSet_nonzero] using
    prob_pi_cubeSet_mem_family (fun _ : α => labelLaw L p hp hLp)
      (fun _ k => decide (k ≠ 0)) ((L : ℝ) * p) hobs D

/-- Dependent rows give the density bound using only a union bound on failures.
The law of the rows and of their union is supplied by the explicit label coupling. -/
theorem familyMeasure_unionFamily_label_lower (L : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hLp : (L : ℝ) * p ≤ 1) (D : Family α) :
    1 - (L : ℝ) * (1 - familyMeasure p D) ≤
      familyMeasure ((L : ℝ) * p) (unionFamily L D) := by
  classical
  have hgood := FiniteLaw.prob_forall_ge_of_const
    (labelSamples (α := α) L p hp hLp)
    (fun (j : Fin L) ω => labelRow ω j ∈ D) (familyMeasure p D)
    (fun j => labelRow_prob_mem_family L p hp hLp j D)
  have hinclusion := (labelSamples (α := α) L p hp hLp).prob_mono
    (P := fun ω => ∀ j : Fin L, labelRow ω j ∈ D)
    (Q := fun ω => unionTuple (labelRow ω) ∈ unionFamily L D)
    (fun ω hω => mem_unionFamily.mpr ⟨labelRow ω, hω, rfl⟩)
  rw [labelUnion_prob_mem_family] at hinclusion
  simpa only [Fintype.card_fin] using hgood.trans hinclusion

end

end TalagrandDiscreteConvexity

end OAI

-- ---- platform node ----
open OAI OAI.TalagrandDiscreteConvexity
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.TalagrandDiscreteConvexity.familyMeasure_unionFamily_label_lower := @_root_.OAI.TalagrandDiscreteConvexity.familyMeasure_unionFamily_label_lower
