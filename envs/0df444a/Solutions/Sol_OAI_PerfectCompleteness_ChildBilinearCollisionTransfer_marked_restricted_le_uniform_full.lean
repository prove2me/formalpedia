-- Prove2me | solution 1 for OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:37.753417+00:00
-- url     : https://prove2.me/submissions/d0e861a3-c19e-4607-ab8c-fbd607a200c7

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.Encoding
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P007
import Definitions.Def_OAIQ252P008
import Definitions.Def_OAIQ252P011
import Theorems.Thm_OAI_PerfectCompleteness_BilinearCollisionTransfer_full_collision_transfer

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Finite weighted Cauchy–Schwarz for probability weights. The summands
need not be nonnegative. -/
theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

end UniqueGamesTheorem.Foundations.Information

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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
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

end
end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_DensityVariation
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DensityVariation

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias

noncomputable section

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem variation_eq_density (μ ν : FiniteDistribution Ω) (density : Ω → ℝ)
    (h : ∀ x, ν.weight x = μ.weight x * density x) :
    ν.totalVariation μ = μ.expectation (fun x => |density x - 1|) / 2 := by
  unfold FiniteDistribution.totalVariation FiniteDistribution.expectation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [h x, show μ.weight x * density x - μ.weight x =
    μ.weight x * (density x - 1) by ring, abs_mul,
    abs_of_nonneg (μ.nonnegative x)]

theorem variation_le_sqrt (μ ν : FiniteDistribution Ω) (density : Ω → ℝ)
    (h : ∀ x, ν.weight x = μ.weight x * density x) (v : ℝ)
    (hv : μ.expectation (fun x => (density x - 1) ^ 2) ≤ v) :
    ν.totalVariation μ ≤ Real.sqrt v / 2 := by
  rw [variation_eq_density μ ν density h]
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.le_sqrt_of_sq_le
  have hcs := UniqueGamesTheorem.Foundations.Information.weighted_sum_sq_le μ.weight
    (fun x => |density x - 1|) ⟨μ.nonnegative, μ.normalized⟩
  change μ.expectation (fun x => |density x - 1|) ^ 2 ≤
    μ.expectation (fun x => |density x - 1| ^ 2) at hcs
  simpa only [sq_abs] using hcs.trans (by simpa only [sq_abs] using hv)

theorem variation_pushforward_le (μ ν : FiniteDistribution Ω) (observe : Ω → Γ) :
    (μ.pushforward observe).totalVariation (ν.pushforward observe) ≤
      μ.totalVariation ν := by
  classical
  unfold FiniteDistribution.totalVariation
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  have hdiff (y : Γ) :
      (μ.pushforward observe).weight y - (ν.pushforward observe).weight y =
        ∑ x, if observe x = y then μ.weight x - ν.weight x else 0 := by
    simp only [FiniteDistribution.pushforward, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : observe x = y <;> simp [hx]
  calc
    _ ≤ ∑ y, ∑ x, if observe x = y then |μ.weight x - ν.weight x| else 0 := by
      apply Finset.sum_le_sum
      intro y _
      rw [hdiff]
      calc
        _ ≤ ∑ x, |if observe x = y then μ.weight x - ν.weight x else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          split <;> simp
    _ = _ := by rw [Finset.sum_comm]; simp

theorem observed_variation_le_sqrt (μ ν : FiniteDistribution Ω) (density : Ω → ℝ)
    (h : ∀ x, ν.weight x = μ.weight x * density x) (v : ℝ)
    (hv : μ.expectation (fun x => (density x - 1) ^ 2) ≤ v)
    (observe : Ω → Γ) :
    (ν.pushforward observe).totalVariation (μ.pushforward observe) ≤ Real.sqrt v / 2 :=
  (variation_pushforward_le ν μ observe).trans (variation_le_sqrt μ ν density h v hv)

end
end PerfectCompleteness.DensityVariation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CollisionAveragingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SparseProjection

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias DensityVariation

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

omit [Fintype I] [DecidableEq I] in
theorem local_second_moment (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (i : I) :
    (P i).expectation (fun x => localDensity β q i x ^ 2) =
      1 + β ^ 2 * (P i).expectation (fun x => (q i x - 1) ^ 2) := by
  calc
    _ = (P i).expectation (fun _ => 1) +
        (2 * β) * ((P i).expectation (q i) - (P i).expectation (fun _ => 1)) +
        β ^ 2 * (P i).expectation (fun x => (q i x - 1) ^ 2) := by
      simp only [FiniteDistribution.expectation, localDensity, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [expectation_const, mean]; ring

theorem density_mean (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) : (FiniteProduct.law P).expectation (density β q) = 1 := by
  change (FiniteProduct.law P).expectation (fun x => ∏ i, localDensity β q i (x i)) = 1
  rw [FiniteProduct.expectation_product]
  simp only [local_mean P q mean, Finset.prod_const_one]

theorem density_second_moment (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) :
    (FiniteProduct.law P).expectation (fun x => (density β q x - 1) ^ 2) =
      (∏ i, (1 + β ^ 2 * (P i).expectation (fun x => (q i x - 1) ^ 2))) - 1 := by
  have identity : (FiniteProduct.law P).expectation (fun x => (density β q x - 1) ^ 2) =
      (FiniteProduct.law P).expectation (fun x => density β q x ^ 2) -
        2 * (FiniteProduct.law P).expectation (density β q) + 1 := by
    calc
      _ = (FiniteProduct.law P).expectation (fun x => density β q x ^ 2) -
          2 * (FiniteProduct.law P).expectation (density β q) +
          (FiniteProduct.law P).expectation (fun _ => 1) := by
        simp only [FiniteDistribution.expectation, Finset.mul_sum,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by rw [expectation_const]
  rw [identity, density_mean P q mean]
  have square : (FiniteProduct.law P).expectation (fun x => density β q x ^ 2) =
      ∏ i, (P i).expectation (fun x => localDensity β q i x ^ 2) := by
    simp only [density, ← Finset.prod_pow]
    exact FiniteProduct.expectation_product P (fun i x => localDensity β q i x ^ 2)
  rw [square]
  simp only [local_second_moment P q mean]
  ring

theorem density_second_moment_le (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (mean : ∀ i, (P i).expectation (q i) = 1)
    (β v : ℝ) (bound : ∀ i, (P i).expectation (fun x => (q i x - 1) ^ 2) ≤ v) :
    (FiniteProduct.law P).expectation (fun x => (density β q x - 1) ^ 2) ≤
      (1 + β ^ 2 * v) ^ Fintype.card I - 1 := by
  rw [density_second_moment P q mean]
  apply sub_le_sub_right
  calc
    _ ≤ ∏ _i : I, (1 + β ^ 2 * v) := by
      apply Finset.prod_le_prod
      · intro i _
        have h : 0 ≤ (P i).expectation (fun x => (q i x - 1) ^ 2) :=
          Finset.sum_nonneg fun x _ => mul_nonneg ((P i).nonnegative x) (sq_nonneg _)
        positivity
      · intro i _
        exact add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left (bound i) (sq_nonneg β))
    _ = _ := by simp

theorem projected_weight (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (x : (i : I) → Ω i) :
    (projectedLaw P q nonnegative mean β hβ hβ').weight x =
      (FiniteProduct.law P).weight x * density β q x := by
  simp only [projectedLaw, FiniteProduct.law, reweight, Finset.prod_mul_distrib, density]

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (P : (i : I) → FiniteDistribution (Ω i))
    (q : (i : I) → Ω i → ℝ) (nonnegative : ∀ i x, 0 ≤ q i x)
    (mean : ∀ i, (P i).expectation (q i) = 1)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (v : ℝ) (bound : ∀ i, (P i).expectation (fun x => (q i x - 1) ^ 2) ≤ v)
    (observe : ((i : I) → Ω i) → Γ) :
    ((projectedLaw P q nonnegative mean β hβ hβ').pushforward observe).totalVariation
        ((FiniteProduct.law P).pushforward observe) ≤
      Real.sqrt ((1 + β ^ 2 * v) ^ Fintype.card I - 1) / 2 :=
  observed_variation_le_sqrt (FiniteProduct.law P) _ (density β q)
    (projected_weight P q nonnegative mean β hβ hβ') _
    (density_second_moment_le P q mean β v bound) observe

end
end PerfectCompleteness.SparseProjection


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformChildSum
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.OddListExtraction.form_atom_self _root_.OAI.PerfectCompleteness.OddListExtraction.multiplicationForm_apply _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformChildSum

open scoped BigOperators
open PointwiseSpaces RecursiveSpaces UniformLinearImage
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {𝕜 X J : Type*} [Field 𝕜] [Fintype J]
  {D : J → Type*}

theorem childSum_surjective (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) : Function.Surjective (childSum r H) := by
  classical
  intro u
  let p : J → Submodule 𝕜 (X → 𝕜) :=
    fun i => (squareSpace (H i)).map (pullback 𝕜 (r i))
  have hu : (u : X → 𝕜) ∈ ⨆ i ∈ (Finset.univ : Finset J), p i := by
    simpa [p, childSpace] using u.property
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (s := Finset.univ) p (u : X → 𝕜)).mp hu
  have hx : ∀ i, ∃ w : squareSpace (H i),
      pullback 𝕜 (r i) (w : D i → 𝕜) = (v i : X → 𝕜) := by
    intro i
    obtain ⟨w, hw, heq⟩ := Submodule.mem_map.mp (v i).property
    exact ⟨⟨w, hw⟩, heq⟩
  choose w hw using hx
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change (∑ i, pullback 𝕜 (r i) (w i : D i → 𝕜)) = (u : X → 𝕜)
  calc
    _ = ∑ i, (v i : X → 𝕜) := Finset.sum_congr rfl (fun i _ => hw i)
    _ = _ := hv


variable {branch : Nat → Nat} {n : Nat}

theorem recursiveSum_surjective (A : Slots branch (n + 1) → Type*) :
    Function.Surjective (recursiveSum (𝕜 := 𝕜) A) :=
  childSum_surjective (childRestriction A) (fun i => space 𝕜 branch n (childFamily A i))

end
end PerfectCompleteness.UniformChildSum

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_KeyFiniteness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalEdges.coarsen_evaluateLabel _root_.OAI.PerfectCompleteness.CanonicalEdges.restore_coarsen _root_.OAI.PerfectCompleteness.CanonicalKeyShape.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalKeyShape.transport_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_decode _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_symm_val _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport
open scoped BigOperators

variable {n : Nat} {Y : Type*}

theorem card_answer (signs : SourceClause.Triple) : Nat.card (Answer signs) = 7 := by
  simpa only [Nat.card_fin] using Nat.card_congr (answerEquivFinSeven signs)

theorem card_slotDomain_le_seven (s : Slot) : Nat.card s.Domain ≤ 7 := by
  cases s with
  | clause occurrence variableIDs signs => exact (card_answer signs).le
  | bit variableID =>
      change Nat.card Bool ≤ 7
      simp

theorem card_assignment_le_seven_pow (slots : Fin n → Slot) :
    Nat.card (Assignment slots) ≤ 7 ^ n := by
  change Nat.card (∀ i : Fin n, (slots i).Domain) ≤ _
  rw [Nat.card_pi]
  calc
    (∏ i : Fin n, Nat.card (slots i).Domain) ≤ ∏ _i : Fin n, (7 : Nat) :=
      Finset.prod_le_prod' (fun i _ => card_slotDomain_le_seven (slots i))
    _ = 7 ^ n := by simp

end PerfectCompleteness.CanonicalKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionOrderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TreeCardinality

open TreeSourceSpaces HierarchicalArrays
open scoped BigOperators

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem domain_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (Domain slots) ≤ domainBound branch n t := by
  change Nat.card (∀ leaf, LeafDomain slots leaf) ≤ _
  rw [Nat.card_pi]
  calc
    _ ≤ ∏ _leaf : RecursiveSpaces.Slots branch n, (7 ^ t : Nat) :=
      Finset.prod_le_prod' (fun leaf _ =>
        CanonicalKeys.card_assignment_le_seven_pow (slots leaf))
    _ = domainBound branch n t := by simp [domainBound]

theorem subspace_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (V : Submodule F2 (Domain slots → F2)) :
    Nat.card V ≤ functionBound branch n t := by
  calc
    Nat.card V ≤ Nat.card (Domain slots → F2) :=
      Nat.card_le_card_of_injective (fun f : V => f.val) Subtype.val_injective
    _ = 2 ^ Nat.card (Domain slots) := by rw [Nat.card_fun, Nat.card_zmod]
    _ ≤ functionBound branch n t :=
      pow_le_pow_right₀ (by decide : (1 : Nat) ≤ 2) (domain_card_le slots)

theorem H_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (H slots) ≤ functionBound branch n t :=
  subspace_card_le slots (H slots)

theorem square_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (PointwiseSpaces.squareSpace (H slots)) ≤ functionBound branch n t :=
  subspace_card_le slots (PointwiseSpaces.squareSpace (H slots))

theorem arrays_card_le
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    Nat.card (Arrays slots rows) ≤ arraysBound branch n t rows := by
  change Nat.card (∀ node : Nodes branch n,
    Fin (rows (Nodes.height node)) → H (nodeSlots slots node)) ≤ _
  rw [Nat.card_pi]
  apply Finset.prod_le_prod'
  intro node _
  rw [Nat.card_fun, Nat.card_fin]
  exact pow_le_pow_left₀ (Nat.zero_le _) (H_card_le (nodeSlots slots node)) _

end
end PerfectCompleteness.TreeCardinality


namespace PerfectCompleteness.ChildBlockCardinality

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem card_le (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Nat.card (Raw calls rows slots) ≤ bound branch n t calls rows := by
  rw [Nat.card_prod, Nat.card_fun, Nat.card_fin]
  exact Nat.mul_le_mul
    (pow_le_pow_left₀ (Nat.zero_le _) (TreeCardinality.square_card_le slots) calls)
    (TreeCardinality.arrays_card_le slots rows)

theorem fintype_card_le (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype.card (Raw calls rows slots) ≤ bound branch n t calls rows := by
  simpa only [Nat.card_eq_fintype_card] using card_le calls rows slots

end
end PerfectCompleteness.ChildBlockCardinality


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CoordinateReplacementLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CoordinateReplacement

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

omit [Fintype I] [DecidableEq I] in

theorem support_of_domination (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a) :
    ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0 := by
  intro i a hzero
  apply le_antisymm
  · simpa only [hzero, mul_zero] using domination i a
  · exact (Q i).nonnegative a

omit [Fintype I] [DecidableEq I] in
theorem ratio_mean_one_of_domination (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a) (i : I) :
    (P i).expectation (ratio P Q i) = 1 :=
  ratio_mean_one_of_support P Q (support_of_domination P Q B domination) i

omit [Fintype I] [DecidableEq I] in
theorem ratio_bounds_of_domination (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (nonnegative : 0 ≤ B)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a)
    (i : I) (a : Ω i) : 0 ≤ ratio P Q i a ∧ ratio P Q i a ≤ B := by
  refine ⟨ratio_nonnegative P Q i a, ?_⟩
  by_cases hzero : (P i).weight a = 0
  · simpa only [ratio, hzero, div_zero] using nonnegative
  · exact (div_le_iff₀ (lt_of_le_of_ne ((P i).nonnegative a) (Ne.symm hzero))).2
      (domination i a)

omit [Fintype I] [DecidableEq I] in

theorem ratio_second_moment_le (P Q : (i : I) → FiniteDistribution (Ω i))
    (B : ℝ) (nonnegative : 0 ≤ B)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a) (i : I) :
    (P i).expectation (fun a => (ratio P Q i a - 1) ^ 2) ≤ B - 1 := by
  have hpoint (a : Ω i) :
      (ratio P Q i a - 1) ^ 2 ≤ (B - 2) * ratio P Q i a + 1 := by
    obtain ⟨hpos, hbound⟩ := ratio_bounds_of_domination P Q B nonnegative domination i a
    have hmul := mul_le_mul_of_nonneg_right hbound hpos
    nlinarith
  have hexpectation :
      (P i).expectation (fun a => (B - 2) * ratio P Q i a + 1) =
        (B - 2) * (P i).expectation (ratio P Q i) + 1 := by
    unfold FiniteDistribution.expectation
    rw [Finset.mul_sum]
    simp only [mul_add, mul_one, Finset.sum_add_distrib]
    rw [(P i).normalized]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    ring
  calc
    _ ≤ (P i).expectation (fun a => (B - 2) * ratio P Q i a + 1) :=
      SmallBias.expectation_mono (P i) hpoint
    _ = (B - 2) * (P i).expectation (ratio P Q i) + 1 := hexpectation
    _ = B - 1 := by
      rw [ratio_mean_one_of_domination P Q B domination i]
      ring


variable [∀ i, Nonempty (Ω i)]

omit [Fintype I] [DecidableEq I] in

theorem uniform_domination (Q : (i : I) → FiniteDistribution (Ω i)) (B : ℝ)
    (cardinality : ∀ i, (Fintype.card (Ω i) : ℝ) ≤ B) (i : I) (a : Ω i) :
    (Q i).weight a ≤ B * (FiniteDistribution.uniform (Ω i)).weight a := by
  classical
  have hweight : (Q i).weight a ≤ 1 := by
    calc
      _ ≤ ∑ b, (Q i).weight b :=
        Finset.single_le_sum (fun b _ => (Q i).nonnegative b) (Finset.mem_univ a)
      _ = 1 := (Q i).normalized
  have hcard : 0 < (Fintype.card (Ω i) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  change (Q i).weight a ≤ B * (1 / (Fintype.card (Ω i) : ℝ))
  calc
    _ ≤ 1 := hweight
    _ ≤ B * (1 / (Fintype.card (Ω i) : ℝ)) := by
      rw [mul_one_div]
      exact (one_le_div hcard).2 (cardinality i)


end
end PerfectCompleteness.CoordinateReplacement



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_MultiplicationFormInjectiveLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SparseReplacement

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CoordinateReplacement

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

omit [Fintype I] [DecidableEq I] in
theorem row_weight (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (i : I) (a : Ω i) :
    (row P Q β hβ hβ' i).weight a =
      (1 - β) * (P i).weight a + β * (Q i).weight a := by
  simp [row, FiniteDistribution.mixture, ProjectionPosterior.bernoulli,
    add_comm]

theorem markedLaw_marginal (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (markedLaw P Q β hβ hβ').pushforward Prod.snd = law P Q β hβ hβ' := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  have hsum : ((markedLaw P Q β hβ hβ').pushforward Prod.snd).weight x =
      ∑ mask : I → Bool,
        (∏ i, (ProjectionPosterior.bernoulli β hβ hβ').weight (mask i)) *
          (∏ i, (if mask i then Q i else P i).weight (x i)) := by
    simp [markedLaw, FiniteDistribution.pushforward, CleanConditioning.kernelJoint,
      Fintype.sum_prod_type, FiniteProduct.law]
  rw [hsum]
  change (∑ mask : I → Bool,
      (∏ i, (ProjectionPosterior.bernoulli β hβ hβ').weight (mask i)) *
        (∏ i, (if mask i then Q i else P i).weight (x i))) =
    ∏ i, ∑ b : Bool, (ProjectionPosterior.bernoulli β hβ hβ').weight b *
      (if b then Q i else P i).weight (x i)
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b =>
    (ProjectionPosterior.bernoulli β hβ hβ').weight b *
      (if b then Q i else P i).weight (x i))).symm

omit [Fintype I] [DecidableEq I] in

theorem ratio_reweight_eq (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0) (i : I) :
    DensityVariation.reweight (P i) (ratio P Q i) (ratio_nonnegative P Q i)
      (ratio_mean_one_of_support P Q support i) = Q i := by
  apply FiniteDistribution.eq_of_weight_eq
  exact weight_mul_ratio_of_support P Q support i

theorem projectedLaw_eq (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    SparseProjection.projectedLaw P (ratio P Q) (ratio_nonnegative P Q)
      (ratio_mean_one_of_support P Q support) β hβ hβ' = law P Q β hβ hβ' := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, (P i).weight (x i) *
      SparseProjection.localDensity β (ratio P Q) i (x i)) =
    ∏ i, (row P Q β hβ hβ' i).weight (x i)
  apply Finset.prod_congr rfl
  intro i _
  rw [row_weight]
  unfold SparseProjection.localDensity
  calc
    _ = (1 - β) * (P i).weight (x i) +
        β * ((P i).weight (x i) * ratio P Q i (x i)) := by ring
    _ = _ := by rw [weight_mul_ratio_of_support P Q support]

theorem forward_eq (P Q : (i : I) → FiniteDistribution (Ω i))
    (support : ∀ i a, (P i).weight a = 0 → (Q i).weight a = 0)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1) :
    ProjectionPosterior.forward P (ratio P Q) (ratio_nonnegative P Q)
      (ratio_mean_one_of_support P Q support) β hβ hβ' =
        markedLaw P Q β hβ hβ'.le := by
  unfold ProjectionPosterior.forward markedLaw
  simp only [ratio_reweight_eq P Q support]

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (P Q : (i : I) → FiniteDistribution (Ω i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (B : ℝ) (hB : 0 ≤ B)
    (domination : ∀ i a, (Q i).weight a ≤ B * (P i).weight a)
    (observe : ((i : I) → Ω i) → Γ) :
    ((law P Q β hβ hβ').pushforward observe).totalVariation
        ((FiniteProduct.law P).pushforward observe) ≤
      Real.sqrt ((1 + β ^ 2 * (B - 1)) ^ Fintype.card I - 1) / 2 := by
  rw [← projectedLaw_eq P Q (support_of_domination P Q B domination) β hβ hβ']
  exact SparseProjection.observed_variation P (ratio P Q) (ratio_nonnegative P Q)
    (ratio_mean_one_of_support P Q (support_of_domination P Q B domination))
    β hβ hβ' (B - 1) (ratio_second_moment_le P Q B hB domination) observe


end
end PerfectCompleteness.SparseReplacement


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_ChildUnmarkedSpace
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildUnmarkedSpace

open RecursiveSpaces TreeSourceSpaces PointwiseSpaces
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem assemble_eq_recursiveSum
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (v : (i : Fin (branch n)) → squareSpace (H (childSlots slots i))) :
    BilinearWitness.assemble (childMap slots) v =
      UniformChildSum.recursiveSum (LeafDomain slots) v := by
  apply Subtype.ext
  simp only [BilinearWitness.assemble, Submodule.coe_sum]
  rfl

theorem assemble_surjective
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    Function.Surjective (BilinearWitness.assemble (childMap slots)) := by
  intro v
  obtain ⟨w, hw⟩ := UniformChildSum.recursiveSum_surjective
    (𝕜 := F2) (LeafDomain slots) v
  exact ⟨w, (assemble_eq_recursiveSum slots w).trans hw⟩

theorem childMap_mem_space
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (mask : Fin (branch n) → Bool) (i : Fin (branch n)) (hi : mask i = false)
    (v : squareSpace (H (childSlots slots i))) : childMap slots i v ∈ space slots mask := by
  have hle : LinearMap.range (childMap slots i) ≤ space slots mask := by
    unfold space
    exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
  exact hle ⟨v, rfl⟩

end
end PerfectCompleteness.ChildUnmarkedSpace

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_ChildBilinearCollisionTransfer
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildBilinearCollisionTransfer

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t : Nat}

variable {Z : Fin (branch n) → Type*} [∀ i, Fintype (Z i)]

theorem marked_restricted_le_uniform_full_oai
    (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (projected : (i : Fin (branch n)) → Z i → Slots branch n → Fin t → MixedSupport.Slot)
    (p : ∀ i z s k, MixedSupport.Projection
      (childSlots slots i s k) (projected i z s k))
    (choiceLaw : (i : Fin (branch n)) → FiniteDistribution (Z i))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β < 1)
    (F₀ F₁ : Raw calls rows slots → Option (ParentForm slots)) :
    (SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform
          (ChildBlockCardinality.Raw calls rows (childSlots slots i)))
        (ChildBlockProjection.replacementLaws calls rows (childSlots slots)
          projected p choiceLaw) β hβ hβ'.le).probability
      (fun z => BilinearCollisionTransfer.restrictedCollision
        (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) ≤
      (FiniteProduct.law (fun i => FiniteDistribution.uniform
        (ChildBlockCardinality.Raw calls rows (childSlots slots i)))).probability
          (fun x => BilinearCollisionTransfer.fullCollision (F₀ x) (F₁ x)) +
        2 * (β * (ChildBlockCardinality.bound branch n t calls rows : ℝ) / (1 - β)) +
        Real.sqrt ((1 + β ^ 2 *
          ((ChildBlockCardinality.bound branch n t calls rows : ℝ) - 1)) ^
            branch n - 1) / 2 := by
  let P : (i : Fin (branch n)) → FiniteDistribution
      (ChildBlockCardinality.Raw calls rows (childSlots slots i)) :=
    fun i => FiniteDistribution.uniform
      (ChildBlockCardinality.Raw calls rows (childSlots slots i))
  let Q := ChildBlockProjection.replacementLaws calls rows (childSlots slots)
    projected p choiceLaw
  let L : ℝ := ChildBlockCardinality.bound branch n t calls rows
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hcard : ∀ i : Fin (branch n),
      (Fintype.card (ChildBlockCardinality.Raw calls rows (childSlots slots i)) : ℝ) ≤ L := by
    intro i
    dsimp only [L]
    exact_mod_cast ChildBlockCardinality.fintype_card_le calls rows (childSlots slots i)
  have hdom : ∀ i x, (Q i).weight x ≤ L * (P i).weight x :=
    CoordinateReplacement.uniform_domination Q L hcard
  have hsupport := CoordinateReplacement.support_of_domination P Q L hdom
  have hbound : ∀ i x, CoordinateReplacement.ratio P Q i x ≤ L :=
    fun i x => (CoordinateReplacement.ratio_bounds_of_domination P Q L hL hdom i x).2
  have htransfer := BilinearCollisionTransfer.full_collision_transfer
    (ChildUnmarkedSpace.childMap slots) (ChildUnmarkedSpace.assemble_surjective slots)
    F₀ F₁ (fun _ mask => ChildUnmarkedSpace.space slots mask)
    (fun _ mask i hi v => ChildUnmarkedSpace.childMap_mem_space slots mask i hi v)
    P (CoordinateReplacement.ratio P Q) (CoordinateReplacement.ratio_nonnegative P Q)
    (CoordinateReplacement.ratio_mean_one_of_support P Q hsupport)
    β hβ hβ' L hL hbound (FiniteProduct.law P)
  rw [SparseReplacement.forward_eq P Q hsupport β hβ hβ',
    SparseReplacement.markedLaw_marginal] at htransfer
  have hvariation := SparseReplacement.observed_variation P Q β hβ hβ'.le L hL hdom
    (id : Raw calls rows slots → Raw calls rows slots)
  simp only [FiniteDistribution.pushforward_id, Fintype.card_fin] at hvariation
  change (SparseReplacement.markedLaw P Q β hβ hβ'.le).probability
      (fun z => BilinearCollisionTransfer.restrictedCollision
        (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) ≤
    (FiniteProduct.law P).probability
      (fun x => BilinearCollisionTransfer.fullCollision (F₀ x) (F₁ x)) +
      2 * (β * L / (1 - β)) +
      Real.sqrt ((1 + β ^ 2 * (L - 1)) ^ branch n - 1) / 2
  linarith

end
end PerfectCompleteness.ChildBilinearCollisionTransfer

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full_oai.{u_1} := @OAI.PerfectCompleteness.ChildBilinearCollisionTransfer.marked_restricted_le_uniform_full_oai.{u_1}
