-- Prove2me | solution 1 for OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:36.424612+00:00
-- url     : https://prove2.me/submissions/9f481e39-e2bb-45e0-be3b-deb0bffbf60e

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Function.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Std
import Definitions.Def_OAIQ252P011

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact finite total variation and its event-probability bound. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- A one-sided event difference is bounded by half the total absolute mass
difference. Normalization is used; the full absolute-mass sum would lose a
factor of two needed in the repetition argument. -/
theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]
end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SmallBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Foundations.Information

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem expectation_mono (μ : FiniteDistribution Ω) {a b : Ω → ℝ}
    (h : ∀ x, a x ≤ b x) : μ.expectation a ≤ μ.expectation b := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

end

end PerfectCompleteness.SmallBias

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteProduct

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem expectation_product (P : (i : I) → FiniteDistribution (Ω i))
    (f : (i : I) → Ω i → ℝ) :
    (law P).expectation (fun x => ∏ i, f i (x i)) =
      ∏ i, (P i).expectation (f i) := by
  change (∑ x : (i : I) → Ω i, (∏ i, (P i).weight (x i)) *
      (∏ i, f i (x i))) = ∏ i, ∑ a, (P i).weight a * f i a
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).weight a * f i a)).symm

omit [∀ index, Fintype (Ω index)] in
theorem product_factor (i : I) (f : Ω i → ℝ) (x : (j : I) → Ω j) :
    (∏ j, factor i f j (x j)) = f (x i) := by
  classical
  rw [Finset.prod_eq_single i]
  · exact factor_self i f (x i)
  · intro j _ h
    exact factor_other i j h f (x j)
  · simp

theorem expectation_factor_product (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) (f : Ω i → ℝ) :
    (∏ j, (P j).expectation (factor i f j)) = (P i).expectation f := by
  classical
  rw [Finset.prod_eq_single i]
  · congr 1
    funext a
    exact factor_self i f a
  · intro j _ h
    rw [factor_function_other i j h, SmallBias.expectation_const]
  · simp

theorem expectation_eval (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) (f : Ω i → ℝ) :
    (law P).expectation (fun x => f (x i)) = (P i).expectation f := by
  calc
    _ = (law P).expectation (fun x => ∏ j, factor i f j (x j)) := by
      apply FiniteDistribution.expectation_congr
      intro x
      exact (product_factor i f x).symm
    _ = ∏ j, (P j).expectation (factor i f j) := expectation_product P _
    _ = _ := expectation_factor_product P i f

end
end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanConditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CleanConditioning

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section


variable {E T R : Type*} [Fintype E] [Fintype T] [Fintype R]

theorem probability_kernelJoint (μ : FiniteDistribution E)
    (kernel : E → FiniteDistribution T) (event : E × T → Bool) :
    (kernelJoint μ kernel).probability event =
      ∑ e, μ.weight e * (kernel e).probability (fun t => event (e, t)) := by
  simp only [FiniteDistribution.probability, kernelJoint, Fintype.sum_prod_type,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro t _
  by_cases h : event (e, t) = true <;> simp [h]


end
end PerfectCompleteness.CleanConditioning

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CollisionAveragingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ProjectionPosterior

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias DensityVariation SparseProjection CleanConditioning

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem posterior_le (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L) (i : I) (x : Ω i) :
    posterior β q i x ≤ β * L / (1 - β) := by
  have hd := localDensity_positive β hβ hβ' q nonnegative i x
  calc
    _ ≤ β * L / localDensity β q i x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (bound i x) hβ) hd.le
    _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hβ hL) (sub_pos.mpr hβ')
      (by unfold localDensity; linarith [mul_nonneg hβ (nonnegative i x)])

theorem forward_reverse_weight (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (mask : I → Bool) (x : (i : I) → Ω i) :
    (forward P q nonnegative mean β hβ hβ').weight (mask, x) =
      (reverse P q nonnegative mean β hβ hβ').weight (x, mask) := by
  change (∏ i, (bernoulli β hβ hβ'.le).weight (mask i)) *
      (∏ i, (if mask i then reweight (P i) (q i) (nonnegative i) (mean i) else P i).weight (x i)) =
    (∏ i, (P i).weight (x i) * localDensity β q i (x i)) *
      (∏ i, (bernoulli (posterior β q i (x i)) _ _).weight (mask i))
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hd := ne_of_gt (localDensity_positive β hβ hβ' q nonnegative i (x i))
  cases hi : mask i <;> simp only [bernoulli, Bool.false_eq_true, ite_false, if_false,
    ite_true, if_true, reweight, posterior]
  · field_simp
    unfold localDensity
    ring
  · field_simp

theorem probability_reverse (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (event : ((i : I) → Ω i) → (I → Bool) → Bool) :
    (forward P q nonnegative mean β hβ hβ').probability (fun z => event z.2 z.1) =
      (reverse P q nonnegative mean β hβ hβ').probability (fun z => event z.1 z.2) := by
  simp only [FiniteDistribution.probability, Fintype.sum_prod_type,
    forward_reverse_weight P q nonnegative mean β hβ hβ']
  exact Finset.sum_comm

end
end PerfectCompleteness.ProjectionPosterior


namespace PerfectCompleteness.AdaptiveProjection

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias ProjectionPosterior CleanConditioning

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem probability_selected_le (μ : FiniteDistribution (I → Bool)) (S : Finset I)
    (t : ℝ) (bound : ∀ i, μ.probability (fun mask => mask i) ≤ t) :
    μ.probability (fun mask => decide (∃ i ∈ S, mask i = true)) ≤ S.card * t := by
  classical
  have indicator (mask : I → Bool) :
      (if ∃ i ∈ S, mask i = true then (1 : ℝ) else 0) ≤
        ∑ i ∈ S, if mask i then (1 : ℝ) else 0 := by
    by_cases h : ∃ i ∈ S, mask i = true
    · obtain ⟨i, hi, hm⟩ := h
      rw [ite_eq_left ⟨i, hi, hm⟩]
      calc
        _ = (if mask i then (1 : ℝ) else 0) := by rw [hm]; rfl
        _ ≤ _ := Finset.single_le_sum (s := S) (a := i)
          (f := fun j : I => if mask j then (1 : ℝ) else 0)
          (fun j _ => by split <;> norm_num) hi
    · rw [ite_eq_right h]
      exact Finset.sum_nonneg fun i _ => by split <;> norm_num
  calc
    _ = μ.expectation (fun mask => if ∃ i ∈ S, mask i = true then 1 else 0) := by
      simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
    _ ≤ μ.expectation (fun mask => ∑ i ∈ S, if mask i then (1 : ℝ) else 0) :=
      expectation_mono μ indicator
    _ = ∑ i ∈ S, μ.probability (fun mask => mask i) := by
      simp only [FiniteDistribution.expectation, FiniteDistribution.probability,
        Finset.mul_sum, mul_ite, mul_one, mul_zero]
      exact Finset.sum_comm
    _ ≤ ∑ _i ∈ S, t := Finset.sum_le_sum fun i _ => bound i
    _ = _ := by simp

variable {Ω : I → Type*} [∀ i, Fintype (Ω i)]

omit [∀ i, Fintype (Ω i)] in
theorem posteriorMask_marginal (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (x : (i : I) → Ω i) (i : I) :
    (posteriorMask β hβ hβ' q nonnegative x).probability (fun mask => mask i) =
      posterior β q i (x i) := by
  calc
    _ = (posteriorMask β hβ hβ' q nonnegative x).expectation
        (fun mask => if mask i then 1 else 0) := by
      simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
    _ = (bernoulli (posterior β q i (x i)) _ _).expectation
        (fun b => if b then 1 else 0) :=
      FiniteProduct.expectation_eval
        (fun j : I => bernoulli (posterior β q j (x j))
          (posterior_nonnegative β hβ hβ' q nonnegative j (x j))
          (posterior_le_one β hβ hβ' q nonnegative j (x j)))
        i (fun b : Bool => if b then 1 else 0)
    _ = _ := by simp [FiniteDistribution.expectation, ProjectionPosterior.bernoulli]

theorem adaptive_selection (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L)
    (select : ((i : I) → Ω i) → Finset I) (m : ℕ)
    (size : ∀ x, (select x).card ≤ m) :
    (forward P q nonnegative mean β hβ hβ').probability
      (fun z => decide (∃ i ∈ select z.2, z.1 i = true)) ≤
        m * (β * L / (1 - β)) := by
  classical
  rw [probability_reverse P q nonnegative mean β hβ hβ'
    (fun x mask => decide (∃ i ∈ select x, mask i = true))]
  unfold reverse
  rw [probability_kernelJoint]
  have hnonneg : 0 ≤ β * L / (1 - β) :=
    div_nonneg (mul_nonneg hβ hL) (le_of_lt (sub_pos.mpr hβ'))
  calc
    _ ≤ ∑ x, (SparseProjection.projectedLaw P q nonnegative mean β hβ hβ'.le).weight x *
        (m * (β * L / (1 - β))) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (FiniteDistribution.nonnegative _ x)
      calc
        _ ≤ (select x).card * (β * L / (1 - β)) :=
          probability_selected_le _ (select x) _ (fun i => by
            rw [posteriorMask_marginal]
            exact posterior_le β hβ hβ' q nonnegative L hL bound i (x i))
        _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast size x) hnonneg
    _ = _ := by rw [← Finset.sum_mul, FiniteDistribution.normalized, one_mul]

end
end PerfectCompleteness.AdaptiveProjection

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearWitnessLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BilinearWitness

open scoped BigOperators

noncomputable section

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]

theorem selected_card_le (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜) :
    (selected f spans B).card ≤ 2 := by
  classical
  unfold selected
  split
  · simp
  · exact (Finset.card_insert_le _ _).trans (by simp)

theorem marked_of_restriction_zero (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f)) (B : H →ₗ[𝕜] H →ₗ[𝕜] 𝕜)
    (nonzero : B ≠ 0) (mask : I → Bool) (U : Submodule 𝕜 H)
    (unchanged : ∀ i, mask i = false → ∀ x, f i x ∈ U)
    (vanishes : ∀ x ∈ U, ∀ y ∈ U, B x y = 0) :
    ∃ i ∈ selected f spans B, mask i = true := by
  classical
  let w := chooseWitness f spans B nonzero
  have hselect : selected f spans B = {w.val.1, w.val.2.1} := by
    simp only [selected, dite_eq_right nonzero, w]
  rw [hselect]
  by_cases hi : mask w.val.1 = true
  · exact ⟨w.val.1, by simp, hi⟩
  by_cases hj : mask w.val.2.1 = true
  · exact ⟨w.val.2.1, by simp, hj⟩
  have hif : mask w.val.1 = false := Bool.eq_false_of_not_eq_true hi
  have hjf : mask w.val.2.1 = false := Bool.eq_false_of_not_eq_true hj
  exact False.elim (w.property (vanishes _ (unchanged _ hif _) _ (unchanged _ hjf _)))

end
end PerfectCompleteness.BilinearWitness


namespace PerfectCompleteness.BilinearProjection

open scoped BigOperators
open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness ProjectionPosterior AdaptiveProjection BilinearWitness

noncomputable section

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem disagreement_probability (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f))
    (F₀ F₁ : ((i : I) → Ω i) → (H →ₗ[𝕜] H →ₗ[𝕜] 𝕜))
    (U : ((i : I) → Ω i) → (I → Bool) → Submodule 𝕜 H)
    (unchanged : ∀ x mask i, mask i = false → ∀ v, f i v ∈ U x mask)
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L) :
    (forward P q nonnegative mean β hβ hβ').probability
      (fun z => decide (F₀ z.2 ≠ F₁ z.2 ∧
        ∀ v ∈ U z.2 z.1, ∀ w ∈ U z.2 z.1, F₀ z.2 v w = F₁ z.2 v w)) ≤
      2 * (β * L / (1 - β)) := by
  classical
  let select := fun x => selected f spans (F₀ x - F₁ x)
  have inclusion : ∀ z : (I → Bool) × ((i : I) → Ω i),
      decide (F₀ z.2 ≠ F₁ z.2 ∧
        ∀ v ∈ U z.2 z.1, ∀ w ∈ U z.2 z.1, F₀ z.2 v w = F₁ z.2 v w) = true →
      decide (∃ i ∈ select z.2, z.1 i = true) = true := by
    intro z hz
    have h := of_decide_eq_true hz
    apply decide_eq_true
    apply marked_of_restriction_zero f spans (F₀ z.2 - F₁ z.2)
      (sub_ne_zero.mpr h.1) z.1 (U z.2 z.1) (unchanged z.2 z.1)
    intro v hv w hw
    simpa only [LinearMap.sub_apply, sub_eq_zero] using h.2 v hv w hw
  exact ((forward P q nonnegative mean β hβ hβ').probability_mono inclusion).trans
    (by simpa only [Nat.cast_ofNat] using
      (adaptive_selection P q nonnegative mean β hβ hβ' L hL bound select 2
        (fun x => selected_card_le f spans (F₀ x - F₁ x))))

end
end PerfectCompleteness.BilinearProjection


namespace PerfectCompleteness.BilinearCollisionTransfer

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness ProjectionPosterior BilinearWitness

noncomputable section

theorem probability_le_add_of_imp {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (p q r : X → Bool)
    (h : ∀ x, p x = true → q x = true ∨ r x = true) :
    μ.probability p ≤ μ.probability q + μ.probability r := by
  simp only [FiniteDistribution.probability, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  cases hp : p x <;> cases hq : q x <;> cases hr : r x <;>
    simp only [Bool.false_eq_true, ite_false, if_false, ite_true, if_true, zero_add, add_zero]
  all_goals first | exact μ.nonnegative x | linarith [μ.nonnegative x] |
    exact False.elim (by simpa [hq, hr] using h x hp)

variable {𝕜 I H : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup H] [Module 𝕜 H]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module 𝕜 (V i)]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem collision_split (a b : Option (Form (𝕜 := 𝕜) (H := H)))
    (U : Submodule 𝕜 H) (h : restrictedCollision a b U = true) :
    fullCollision a b = true ∨
      decide (a.getD 0 ≠ b.getD 0 ∧
        ∀ v ∈ U, ∀ w ∈ U, a.getD 0 v w = b.getD 0 v w) = true := by
  obtain ⟨F, G, ha, hb, heq⟩ := of_decide_eq_true h
  subst a b
  by_cases hFG : F = G
  · left
    apply decide_eq_true
    exact ⟨F, rfl, congrArg some hFG.symm⟩
  · right
    simpa only [Option.getD_some, decide_eq_true_eq] using And.intro hFG heq

theorem restricted_le_full_add (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f))
    (F₀ F₁ : ((i : I) → Ω i) → Option (Form (𝕜 := 𝕜) (H := H)))
    (U : ((i : I) → Ω i) → (I → Bool) → Submodule 𝕜 H)
    (unchanged : ∀ x mask i, mask i = false → ∀ v, f i v ∈ U x mask)
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L) :
    (forward P q nonnegative mean β hβ hβ').probability
        (fun z => restrictedCollision (F₀ z.2) (F₁ z.2) (U z.2 z.1)) ≤
      ((forward P q nonnegative mean β hβ hβ').pushforward Prod.snd).probability
        (fun x => fullCollision (F₀ x) (F₁ x)) + 2 * (β * L / (1 - β)) := by
  have hsplit := probability_le_add_of_imp (forward P q nonnegative mean β hβ hβ')
    (fun z => restrictedCollision (F₀ z.2) (F₁ z.2) (U z.2 z.1))
    (fun z => fullCollision (F₀ z.2) (F₁ z.2))
    (fun z => decide ((F₀ z.2).getD 0 ≠ (F₁ z.2).getD 0 ∧
      ∀ v ∈ U z.2 z.1, ∀ w ∈ U z.2 z.1,
        (F₀ z.2).getD 0 v w = (F₁ z.2).getD 0 v w))
    (fun z => collision_split (F₀ z.2) (F₁ z.2) (U z.2 z.1))
  have hbad := BilinearProjection.disagreement_probability f spans
    (fun x => (F₀ x).getD 0) (fun x => (F₁ x).getD 0) U unchanged
    P q nonnegative mean β hβ hβ' L hL bound
  rw [FiniteDistribution.probability_pushforward]
  exact hsplit.trans (add_le_add (le_refl _) hbad)

theorem full_collision_transfer_oai (f : (i : I) → V i →ₗ[𝕜] H)
    (spans : Function.Surjective (assemble f))
    (F₀ F₁ : ((i : I) → Ω i) → Option (Form (𝕜 := 𝕜) (H := H)))
    (U : ((i : I) → Ω i) → (I → Bool) → Submodule 𝕜 H)
    (unchanged : ∀ x mask i, mask i = false → ∀ v, f i v ∈ U x mask)
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (L : ℝ) (hL : 0 ≤ L) (bound : ∀ i x, q i x ≤ L)
    (ν : FiniteDistribution ((i : I) → Ω i)) :
    (forward P q nonnegative mean β hβ hβ').probability
        (fun z => restrictedCollision (F₀ z.2) (F₁ z.2) (U z.2 z.1)) -
      2 * (β * L / (1 - β)) -
      ((forward P q nonnegative mean β hβ hβ').pushforward Prod.snd).totalVariation ν ≤
      ν.probability (fun x => fullCollision (F₀ x) (F₁ x)) := by
  have h := restricted_le_full_add f spans F₀ F₁ U unchanged
    P q nonnegative mean β hβ hβ' L hL bound
  have htv := FiniteDistribution.probability_le_add_totalVariation
    ((forward P q nonnegative mean β hβ hβ').pushforward Prod.snd) ν
    (fun x => fullCollision (F₀ x) (F₁ x))
  linarith

end
end PerfectCompleteness.BilinearCollisionTransfer

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.PerfectCompleteness.BilinearCollisionTransfer.full_collision_transfer_oai.{u_1, u_2, u_3, u_4, u_5}
