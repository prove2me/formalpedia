-- Prove2me | solution 1 for OAI.PerfectCompleteness.UniformCleanSoundness.source_soundness
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:46.638083+00:00
-- url     : https://prove2.me/submissions/a6a75e86-06bf-430a-9449-f2a247986c0a

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
import Mathlib.Data.Fin.Tuple.Basic
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
import Mathlib.LinearAlgebra.Contraction
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
import Definitions.Def_OAIQ252P011

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

theorem probability_inter_eq_mul_conditional (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given) :
    μ.probability (fun x => given x && event x) =
      μ.probability given * (μ.condition given positive).probability event := by
  have h := (eq_div_iff (ne_of_gt positive)).mp
    (μ.probability_condition given event positive)
  simpa only [mul_comm] using h.symm

theorem probability_and_le_left (μ : FiniteDistribution Ω) (event event' : Ω → Bool) :
    μ.probability (fun x => event x && event' x) ≤ μ.probability event := by
  apply μ.probability_mono
  intro x hx
  have h : event x = true ∧ event' x = true := by simpa using hx
  exact h.1

theorem probability_and_eq_zero_of_probability_eq_zero (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (zero : μ.probability given = 0) :
    μ.probability (fun x => given x && event x) = 0 := by
  apply le_antisymm
  · exact (μ.probability_and_le_left given event).trans_eq zero
  · exact μ.probability_nonnegative _

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability_condition_given _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Finite shared randomness is an actual convex mixture of distributions. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]

theorem probability_mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) :
    (seedLaw.mixture laws).probability event =
      ∑ seed, seedLaw.weight seed * (laws seed).probability event := by
  unfold probability mixture
  calc
    _ = ∑ x, ∑ seed,
        seedLaw.weight seed * (if event x then (laws seed).weight x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      cases event x <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [Finset.mul_sum]

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
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Coordinate reindexing for actual finite distributions and repeated games.
The joint questions are iid across coordinates; coordinate-success events
need not be independent. Strategies permute each player's local questions
and answers, so the resulting strategies remain local.
-/

noncomputable section

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

namespace FiniteDistribution

theorem pushforward_equiv {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (e : Ω ≃ Γ) :
    μ.pushforward e = μ.transport e := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward, transport]
  have he : ∀ x : Ω, (e x = y) = (x = e.symm y) := by
    intro x
    apply propext
    constructor
    · intro h
      simpa using congrArg e.symm h
    · intro h
      rw [h, e.apply_symm_apply]
  simp_rw [he]
  simp

theorem table_const_reindex {ι κ Ω : Type*}
    [Fintype ι] [Fintype κ] [Fintype Ω] [DecidableEq ι] [DecidableEq κ]
    (μ : FiniteDistribution Ω) (e : κ ≃ ι) :
    (table (fun _ : ι => μ)).pushforward (fun f => f ∘ e) =
      table (fun _ : κ => μ) := by
  classical
  change (table (fun _ : ι => μ)).pushforward (reindexEquiv e) = _
  rw [pushforward_equiv]
  apply eq_of_weight_eq
  intro g
  change (∏ i : ι, μ.weight (g (e.symm i))) = ∏ k : κ, μ.weight (g k)
  exact e.symm.prod_comp (fun k => μ.weight (g k))

end FiniteDistribution

end UniqueGamesTheorem.Foundations.Games

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
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
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability_condition_given _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact composition identities for finite distribution maps. -/
namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanConditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
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

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem condition_law_all (P : (i : I) → FiniteDistribution (Ω i))
    (event : (i : I) → Ω i → Bool)
    (positive : 0 < (law P).probability (allEvent event)) :
    (law P).condition (allEvent event) positive =
      law (fun i => (P i).condition (event i)
        (coordinate_probability_positive P event positive i)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (if allEvent event x then
      (∏ i, (P i).weight (x i)) / (law P).probability (allEvent event) else 0) =
    ∏ i, if event i (x i) then
      (P i).weight (x i) / (P i).probability (event i) else 0
  rw [← product_filter]
  simp only [allEvent, decide_eq_true_eq, probability_law_all,
    Finset.prod_div_distrib]

end Product


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

theorem probability_kernelJoint_fiber [DecidableEq E] (μ : FiniteDistribution E)
    (kernel : E → FiniteDistribution T) (event : E × T → Bool) (e : E) :
    (kernelJoint μ kernel).probability
      (fun x => decide (x.1 = e) && event x) =
      μ.weight e * (kernel e).probability (fun t => event (e, t)) := by
  rw [probability_kernelJoint]
  rw [Finset.sum_eq_single e]
  · simp
  · intro e' _ hne
    simp [hne, FiniteDistribution.probability]
  · simp

theorem probability_kernelJoint_constant (μ : FiniteDistribution E)
    (kernel : E → FiniteDistribution T) (event : E × T → Bool) (p : ℝ)
    (constant : ∀ e, (kernel e).probability (fun t => event (e, t)) = p) :
    (kernelJoint μ kernel).probability event = p := by
  rw [probability_kernelJoint]
  simp_rw [constant]
  rw [← Finset.sum_mul, μ.normalized, one_mul]

theorem source_condition_of_constant [DecidableEq E] (μ : FiniteDistribution E)
    (kernel : E → FiniteDistribution T) (event : E × T → Bool) (p : ℝ)
    (constant : ∀ e, (kernel e).probability (fun t => event (e, t)) = p)
    (positive : 0 < (kernelJoint μ kernel).probability event) :
    ((kernelJoint μ kernel).condition event positive).pushforward Prod.fst = μ := by
  classical
  have hp : 0 < p := by
    rwa [probability_kernelJoint_constant μ kernel event p constant] at positive
  apply FiniteDistribution.eq_of_weight_eq
  intro e
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.probability_pushforward, FiniteDistribution.probability_condition]
  have hevent : (fun x : E × T => event x && decide (x.1 = e)) =
      (fun x => decide (x.1 = e) && event x) := by
    funext x
    exact Bool.and_comm _ _
  rw [hevent, probability_kernelJoint_fiber, constant,
    probability_kernelJoint_constant μ kernel event p constant]
  exact mul_div_cancel_right₀ _ (ne_of_gt hp)

theorem designated_source_condition [DecidableEq E] [DecidableEq R]
    (μ : FiniteDistribution E) (ν : FiniteDistribution R)
    (kernel : E → R → FiniteDistribution T) (clean : E → R → T → Bool)
    (p : ℝ) (constant : ∀ e r, (kernel e r).probability (clean e r) = p)
    (record : R)
    (positive : 0 <
      (kernelJoint μ (fun e => kernelJoint ν (kernel e))).probability
        (fun x => decide (x.2.1 = record) && clean x.1 x.2.1 x.2.2)) :
    ((kernelJoint μ (fun e => kernelJoint ν (kernel e))).condition
      (fun x => decide (x.2.1 = record) && clean x.1 x.2.1 x.2.2) positive).pushforward
        Prod.fst = μ := by
  apply source_condition_of_constant μ _ _ (ν.weight record * p) _ positive
  intro e
  rw [probability_kernelJoint_fiber]
  rw [constant]


end
end PerfectCompleteness.CleanConditioning

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanCountingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CleanCounting

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning

noncomputable section

theorem expectation_event_factor {A : Type*} [Fintype A]
    (μ : FiniteDistribution A) (event : A → Bool) (a : ℝ) :
    μ.expectation (fun x => if event x then a else 1) =
      1 - (1 - a) * μ.probability event := by
  have hpoint (x : A) : μ.weight x * (if event x then a else 1) =
      μ.weight x - (1 - a) * (if event x then μ.weight x else 0) := by
    cases event x <;> simp
    ring
  change (∑ x, μ.weight x * (if event x then a else 1)) = _
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, μ.normalized]
  rfl

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

omit [DecidableEq I] [∀ i, Fintype (Ω i)] in
theorem power_cleanCount (clean : (i : I) → Ω i → Bool)
    (x : (i : I) → Ω i) (a : ℝ) :
    a ^ cleanCount clean x = ∏ i, if clean i (x i) = true then a else 1 := by
  rw [← Finset.prod_filter]
  simp [cleanCount]

theorem cleanCount_moment (P : (i : I) → FiniteDistribution (Ω i))
    (clean : (i : I) → Ω i → Bool) (a : ℝ) :
    (law P).expectation (fun x => a ^ cleanCount clean x) =
      ∏ i : I, (1 - (1 - a) * (P i).probability (clean i)) := by
  calc
    _ = (law P).expectation (fun x => ∏ i : I, if clean i (x i) then a else 1) :=
      FiniteDistribution.expectation_congr _
        (fun x => power_cleanCount (I := I) (Ω := Ω) clean x a)
    _ = ∏ i : I, (P i).expectation (fun x => if clean i x then a else 1) :=
      expectation_product (I := I) (Ω := Ω) P
        (fun (i : I) (x : Ω i) => if clean i x then a else 1)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      exact expectation_event_factor (P i) (clean i) a


variable {E R T : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (T i)]

omit [Fintype I] [DecidableEq I] in
theorem kernel_clean_probability
    (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (kernel : (i : I) → E i → R i → FiniteDistribution (T i))
    (clean : (i : I) → E i → R i → T i → Bool) (p : I → ℝ)
    (constant : ∀ i e r, (kernel i e r).probability (clean i e r) = p i) (i : I) :
    (kernelJoint (μ i) (fun e => kernelJoint (ν i) (kernel i e))).probability
      (fun x => clean i x.1 x.2.1 x.2.2) = p i := by
  apply probability_kernelJoint_constant (μ i) _ _ (p i)
  intro e
  apply probability_kernelJoint_constant (ν i) _ _ (p i)
  intro r
  exact constant i e r


end
end PerfectCompleteness.CleanCounting


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_RepetitionRateLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.IndexedRepetition

open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {E Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

theorem law_const_fin (μ : FiniteDistribution E) (n : Nat) :
    law (fun _ : Fin n => μ) = μ.iid n := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  rfl

theorem game_fin (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (n : Nat) :
    game G (Fin n) = G.repetition n := by
  unfold game OccurrenceGame.repetition
  simp only [law_const_fin]
  congr 1
  funext x a b
  by_cases h : ∀ i : Fin n, G.accepts (x i) (a i) (b i) = true <;>
    simp only [h, decide_false]

theorem reindex_law {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (μ : FiniteDistribution E) (e : J ≃ I) :
    (law (fun _ : I => μ)).pushforward (fun x => x ∘ e) =
      law (fun _ : J => μ) :=
  FiniteDistribution.table_const_reindex μ e

theorem reindex_success {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (e : J ≃ I)
    (s : Strategy (I → Q₁) (I → Q₂) (I → A₁) (I → A₂)) :
    (game G J).success (reindexStrategy e s) = (game G I).success s := by
  classical
  change (law (fun _ : J => G.occurrences)).probability _ =
    (law (fun _ : I => G.occurrences)).probability _
  rw [← reindex_law G.occurrences e, FiniteDistribution.probability_pushforward]
  apply congrArg (law (fun _ : I => G.occurrences)).probability
  funext x
  have hl : (fun j => G.left ((x ∘ e) j)) ∘ e.symm = fun i => G.left (x i) := by
    funext i
    simp only [Function.comp_apply, e.apply_symm_apply]
  have hr : (fun j => G.right ((x ∘ e) j)) ∘ e.symm = fun i => G.right (x i) := by
    funext i
    simp only [Function.comp_apply, e.apply_symm_apply]
  change decide (∀ j, G.accepts ((x ∘ e) j)
      (s.1 ((fun j => G.left ((x ∘ e) j)) ∘ e.symm) (e j))
      (s.2 ((fun j => G.right ((x ∘ e) j)) ∘ e.symm) (e j)) = true) =
    decide (∀ i, G.accepts (x i)
      (s.1 (fun i => G.left (x i)) i) (s.2 (fun i => G.right (x i)) i) = true)
  rw [hl, hr]
  congr 1
  apply propext
  constructor
  · intro h i
    simpa only [Function.comp_apply, e.apply_symm_apply] using h (e.symm i)
  · intro h j
    exact h (e j)

theorem success_le_repetition_value {I : Type*} [Fintype I] [DecidableEq I]
    [Nonempty A₁] [Nonempty A₂]
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (s : Strategy (I → Q₁) (I → Q₂) (I → A₁) (I → A₂)) :
    (game G I).success s ≤ (G.repetition (Fintype.card I)).value := by
  rw [← reindex_success G (Fintype.equivFin I).symm s, game_fin]
  exact (G.repetition (Fintype.card I)).success_le_value _

end
end PerfectCompleteness.IndexedRepetition

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DesignatedLeavesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.FiniteConditioningBounds

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem condition_probability_mono_on (P : FiniteDistribution Ω)
    (given event target : Ω → Bool) (positive : 0 < P.probability given)
    (inclusion : ∀ x, given x = true → event x = true → target x = true) :
    (P.condition given positive).probability event ≤
      (P.condition given positive).probability target := by
  rw [FiniteDistribution.probability_condition, FiniteDistribution.probability_condition]
  apply div_le_div_of_nonneg_right _ positive.le
  apply P.probability_mono
  intro x hx
  have hx' : given x = true ∧ event x = true := by simpa using hx
  simpa using And.intro hx'.1 (inclusion x hx'.1 hx'.2)

theorem sum_record_inter {R : Type*} [Fintype R] [DecidableEq R]
    (P : FiniteDistribution Ω) (record : Ω → R) (event : Ω → Bool) :
    (∑ r : R, P.probability (fun x => decide (record x = r) && event x)) =
      P.probability event := by
  unfold FiniteDistribution.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x <;> simp [he]

theorem sum_record_weight {R : Type*} [Fintype R] [DecidableEq R]
    (P : FiniteDistribution Ω) (record : Ω → R) (bound : R → ℝ) :
    (∑ r : R, P.probability (fun x => decide (record x = r)) * bound r) =
      P.expectation (fun x => bound (record x)) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

theorem probability_le_record_bound {R : Type*} [Fintype R] [DecidableEq R]
    (P : FiniteDistribution Ω) (record : Ω → R) (event : Ω → Bool)
    (bound : R → ℝ)
    (conditional : ∀ r (positive : 0 < P.probability (fun x => decide (record x = r))),
      (P.condition (fun x => decide (record x = r)) positive).probability event ≤ bound r) :
    P.probability event ≤ P.expectation (fun x => bound (record x)) := by
  rw [← sum_record_inter P record event, ← sum_record_weight P record bound]
  apply Finset.sum_le_sum
  intro r _
  by_cases positive : 0 < P.probability (fun x => decide (record x = r))
  · rw [P.probability_inter_eq_mul_conditional _ _ positive]
    exact mul_le_mul_of_nonneg_left (conditional r positive) (P.probability_nonnegative _)
  · have zero : P.probability (fun x => decide (record x = r)) = 0 :=
      le_antisymm (le_of_not_gt positive) (P.probability_nonnegative _)
    rw [P.probability_and_eq_zero_of_probability_eq_zero _ _ zero, zero, zero_mul]

section Game

variable {E Q₁ Q₂ A₁ A₂ I : Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype I] [DecidableEq I] [Nonempty A₁] [Nonempty A₂]

theorem conditioned_source_success (P : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < P.probability given)
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂) (source : Ω → I → E)
    (source_law : (P.condition given positive).pushforward source =
      law (fun _ : I => G.occurrences))
    (strategy : Strategy (I → Q₁) (I → Q₂) (I → A₁) (I → A₂))
    (inclusion : ∀ x, given x = true → event x = true →
      (IndexedRepetition.game G I).wins strategy (source x) = true) :
    (P.condition given positive).probability event ≤
      (G.repetition (Fintype.card I)).value := by
  have hsource := congrArg
    (fun D : FiniteDistribution (I → E) =>
      D.probability ((IndexedRepetition.game G I).wins strategy)) source_law
  rw [FiniteDistribution.probability_pushforward] at hsource
  calc
    _ ≤ (P.condition given positive).probability
        (fun x => (IndexedRepetition.game G I).wins strategy (source x)) :=
      condition_probability_mono_on P given event _ positive inclusion
    _ = (IndexedRepetition.game G I).success strategy := hsource
    _ ≤ _ := IndexedRepetition.success_le_repetition_value G strategy

end Game

theorem independent_clean_bound {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i, Fintype (A i)]
    {R : Type*} [Fintype R] [DecidableEq R]
    (P : (i : I) → FiniteDistribution (A i))
    (clean : (i : I) → A i → Bool) (record : ((i : I) → A i) → R)
    (count : R → Nat)
    (count_eq : ∀ x, count (record x) = CleanCounting.cleanCount clean x)
    (event : ((i : I) → A i) → Bool) (a : ℝ)
    (conditional : ∀ r (positive : 0 <
      (law P).probability (fun x => decide (record x = r))),
      ((law P).condition (fun x => decide (record x = r)) positive).probability event ≤
        a ^ count r) :
    (law P).probability event ≤
      ∏ i : I, (1 - (1 - a) * (P i).probability (clean i)) := by
  calc
    _ ≤ (law P).expectation (fun x => a ^ count (record x)) :=
      probability_le_record_bound (law P) record event (fun r => a ^ count r) conditional
    _ = (law P).expectation (fun x => a ^ CleanCounting.cleanCount clean x) := by
      apply FiniteDistribution.expectation_congr
      intro x
      rw [count_eq]
    _ = _ := CleanCounting.cleanCount_moment P clean a

end
end PerfectCompleteness.FiniteConditioningBounds

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuarterBalanceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.SelectedSources

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning

noncomputable section

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem expectation_product_selected (P : (i : I) → FiniteDistribution (Ω i))
    (selected : I → Prop) [DecidablePred selected]
    (f : (i : Subtype selected) → Ω i → ℝ) :
    (law P).expectation (fun x => ∏ i : Subtype selected, f i (x i)) =
      ∏ i : Subtype selected, (P i).expectation (f i) := by
  let g : (i : I) → Ω i → ℝ := fun i a =>
    if h : selected i then f ⟨i, h⟩ a else 1
  have hprod (x : (i : I) → Ω i) :
      (∏ i, g i (x i)) = ∏ i : Subtype selected, f i (x i) := by
    simp only [g, Fintype.prod_dite, Finset.prod_const_one, mul_one]
  have hexp (i : I) : (P i).expectation (g i) =
      if h : selected i then (P i).expectation (f ⟨i, h⟩) else 1 := by
    by_cases hi : selected i <;> simp [g, hi, SmallBias.expectation_const]
  calc
    _ = (law P).expectation (fun x => ∏ i, g i (x i)) :=
      FiniteDistribution.expectation_congr _ (fun x => (hprod x).symm)
    _ = ∏ i, (P i).expectation (g i) := expectation_product P g
    _ = ∏ i, if h : selected i then (P i).expectation (f ⟨i, h⟩) else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      exact hexp i
    _ = _ := by simp only [Fintype.prod_dite, Finset.prod_const_one, mul_one]

theorem pushforward_law_selected (P : (i : I) → FiniteDistribution (Ω i))
    (selected : I → Prop) [DecidablePred selected]
    {Γ : Subtype selected → Type*} [∀ i, Fintype (Γ i)]
    (source : (i : Subtype selected) → Ω i → Γ i) :
    (law P).pushforward (fun x (i : Subtype selected) => source i (x i)) =
      law (fun i : Subtype selected => (P i).pushforward (source i)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  calc
    _ = (law P).expectation
        (fun x => if (fun i : Subtype selected => source i (x i)) = y then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : (fun i : Subtype selected => source i (x i)) = y <;> simp [h]
    _ = (law P).expectation
        (fun x => ∏ i : Subtype selected, if source i (x i) = y i then 1 else 0) := by
      apply FiniteDistribution.expectation_congr
      intro x
      simp only [Fintype.prod_boole, funext_iff]
    _ = ∏ i : Subtype selected, (P i).expectation
        (fun a => if source i a = y i then 1 else 0) :=
      expectation_product_selected (I := I) (Ω := Ω) P selected
        (fun (i : Subtype selected) (a : Ω i) => if source i a = y i then (1 : ℝ) else 0)
    _ = _ := by
      simp [law, FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]

theorem selected_sources_conditioned (P : (i : I) → FiniteDistribution (Ω i))
    (event : (i : I) → Ω i → Bool)
    (positive : 0 < (law P).probability (allEvent event))
    (selected : I → Prop) [DecidablePred selected]
    {Γ : Subtype selected → Type*} [∀ i, Fintype (Γ i)]
    (source : (i : Subtype selected) → Ω i → Γ i)
    (μ : (i : Subtype selected) → FiniteDistribution (Γ i))
    (row : ∀ i : Subtype selected,
      ((P i).condition (event i) (coordinate_probability_positive P event positive i)).pushforward
        (source i) = μ i) :
    ((law P).condition (allEvent event) positive).pushforward
      (fun x (i : Subtype selected) => source i (x i)) = law μ := by
  rw [condition_law_all, pushforward_law_selected]
  congr 1
  funext i
  exact row i

end Product


end
end PerfectCompleteness.SelectedSources



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatent
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformLatent

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning

noncomputable section

theorem probability_uniform_singleton {A : Type*} [Fintype A] [Nonempty A]
    [DecidableEq A] (a : A) :
    (FiniteDistribution.uniform A).probability (fun x => decide (x = a)) =
      1 / (Fintype.card A : ℝ) := by
  simp [FiniteDistribution.probability, FiniteDistribution.uniform]


variable {S J : Type*} [Fintype S] [Fintype J] [DecidableEq J]
  (Ω : S → J → Type*) [∀ s j, Fintype (Ω s j)] [∀ s j, Nonempty (Ω s j)]

variable [∀ s j, DecidableEq (Ω s j)]

theorem probability_latentKernel_zero (zero : (s : S) → (j : J) → Ω s j) (s : S) :
    (latentKernel Ω s).probability (zeroEvent Ω zero) =
      ∏ j, 1 / (Fintype.card (Ω s j) : ℝ) := by
  rw [latentKernel, FiniteDistribution.probability_pushforward]
  have hevent : (fun x => zeroEvent Ω zero (⟨s, x⟩ : Raw Ω)) =
      allEvent (fun j a => decide (a = zero s j)) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    simp [zeroEvent, allEvent]
  rw [hevent, probability_law_all]
  apply Finset.prod_congr rfl
  intro j _
  exact probability_uniform_singleton (zero s j)


variable {D : Type*} [Fintype D]

theorem probability_projectedKernel_zero (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D)
    (zero : (s : S) → (j : J) → Ω s j) (s : S) :
    (projectedKernel Ω flag nonprojected s).probability (projectedZero Ω zero) =
      flag.weight true * (∏ j, 1 / (Fintype.card (Ω s j) : ℝ)) := by
  simp [projectedKernel, FiniteDistribution.probability_mixture,
    FiniteDistribution.probability_pushforward, projectedZero,
    probability_latentKernel_zero]

theorem probability_projectedKernel_zero_constant (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D)
    (zero : (s : S) → (j : J) → Ω s j) (cardinality : J → Nat)
    (same_cardinality : ∀ s j, Fintype.card (Ω s j) = cardinality j) (s : S) :
    (projectedKernel Ω flag nonprojected s).probability (projectedZero Ω zero) =
      flag.weight true * (∏ j, 1 / (cardinality j : ℝ)) := by
  rw [probability_projectedKernel_zero]
  simp only [same_cardinality]


end
end PerfectCompleteness.UniformLatent

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CutChildCleanLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.UniformCleanSources

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning SelectedSources UniformLatent

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J D : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E i × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]

omit [∀ index, DecidableEq (D index)] in
theorem clean_source_law
    (μ : (i : I) → FiniteDistribution (E i))
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i))
    (zero : (i : I) → (s : E i × R i) → (j : J i) → Ω i s j)
    (cardinality : (i : I) → J i → Nat)
    (same_cardinality : ∀ i s j, Fintype.card (Ω i s j) = cardinality i j)
    (record : (i : I) → Record (D := D) Ω i)
    (positive : 0 < (childrenLaw Ω μ ν flag nonprojected).probability
      (recordEvent (D := D) Ω zero record)) :
    ((childrenLaw Ω μ ν flag nonprojected).condition (recordEvent (D := D) Ω zero record)
      positive).pushforward (Γ := (i : CleanIndices Ω record) → E i.1)
        (fun x (i : CleanIndices Ω record) => (x i.1).1) =
      law (I := CleanIndices Ω record) (Ω := fun i : CleanIndices Ω record => E i.1)
        (fun i : CleanIndices Ω record => μ i.1) := by
  classical
  let P := fun i => kernelJoint (μ i) (fun e =>
    kernelJoint (ν i) (childKernel Ω flag nonprojected i e))
  let event := rowEvent Ω zero record
  have hpositive : 0 < (law P).probability (allEvent event) := positive
  apply selected_sources_conditioned (I := I)
    (Ω := fun i => E i × (R i × ChildRaw (D := D) Ω i)) P event hpositive
    (fun i => cleanRecord Ω (record i) = true)
    (fun _ x => x.1) (fun i => μ i.1)
  intro i
  have hr : ∃ r, record i.1 = Sum.inr r := by
    have hi := i.property
    cases hrec : record i.1 with
    | inl raw => simp [cleanRecord, hrec] at hi
    | inr r => exact ⟨r, rfl⟩
  obtain ⟨r, hr⟩ := hr
  have hevent : event i.1 =
      (fun x => decide (x.2.1 = r) && childClean (D := D) Ω zero i.1 x.1 x.2.1 x.2.2) := by
    funext x
    cases hclean : childClean (D := D) Ω zero i.1 x.1 x.2.1 x.2.2 <;>
      simp [event, rowEvent, hr, childObservation, hclean]
  have hp := coordinate_probability_positive P event hpositive i.1
  rw [hevent] at hp
  have hconst : ∀ e r, (childKernel Ω flag nonprojected i.1 e r).probability
      (childClean (D := D) Ω zero i.1 e r) =
      (flag i.1).weight true * ∏ j, 1 / (cardinality i.1 j : ℝ) := by
    intro e r
    exact probability_projectedKernel_zero_constant (Ω i.1) (flag i.1) (nonprojected i.1)
      (zero i.1) (cardinality i.1) (same_cardinality i.1) (e, r)
  simpa only [hevent] using
    designated_source_condition (μ i.1) (ν i.1) (childKernel Ω flag nonprojected i.1)
      (childClean (D := D) Ω zero i.1)
      ((flag i.1).weight true * ∏ j, 1 / (cardinality i.1 j : ℝ)) hconst r hp

end
end PerfectCompleteness.UniformCleanSources



namespace PerfectCompleteness.UniformCleanSoundness

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning SelectedSources UniformLatent UniformCleanSources
open FiniteConditioningBounds

noncomputable section

attribute [local instance] Classical.propDecidable

variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  {R J D : I → Type*}
  [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (R i)] [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]

omit [DecidableEq I] [Fintype E] [DecidableEq E]
  [∀ index, Fintype (R index)] [∀ index, Fintype (D index)]
  [∀ index, DecidableEq (R index)] [∀ index, DecidableEq (J index)]
  [∀ index, DecidableEq (D index)]
  [∀ index seed coord, Fintype (Ω index seed coord)]
  [∀ index seed coord, Nonempty (Ω index seed coord)] in
theorem observed_clean_count
    (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (x : Sample (D := D) Ω) :
    Fintype.card (CleanIndices Ω (observations (D := D) Ω zero x)) =
      CleanCounting.cleanCount
        (fun i y => childClean (D := D) Ω zero i y.1 y.2.1 y.2.2) x := by
  classical
  change Fintype.card {i : I //
      cleanRecord Ω (observations (D := D) Ω zero x i) = true} = _
  rw [Fintype.card_subtype]
  unfold CleanCounting.cleanCount
  congr 1
  ext i
  cases h : childClean (D := D) Ω zero i (x i).1 (x i).2.1 (x i).2.2 <;>
    simp [observations, childObservation, cleanRecord, h]

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Nonempty A₁] [Nonempty A₂]

omit [∀ index, DecidableEq (D index)] in
theorem conditional_source_bound
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E × R i → FiniteDistribution (D i))
    (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (cardinality : (i : I) → J i → Nat)
    (same_cardinality : ∀ i s j, Fintype.card (Ω i s j) = cardinality i j)
    (record : FullRecord (D := D) Ω)
    (positive : 0 < (childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected).probability
      (recordEvent (D := D) Ω zero record))
    (event : Sample (D := D) Ω → Bool)
    (strategy : Strategy (CleanIndices Ω record → Q₁) (CleanIndices Ω record → Q₂)
      (CleanIndices Ω record → A₁) (CleanIndices Ω record → A₂))
    (inclusion : ∀ x, recordEvent (D := D) Ω zero record x = true → event x = true →
      (IndexedRepetition.game G (CleanIndices Ω record)).wins strategy
        (fun i => (x i.1).1) = true) :
    ((childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected).condition
      (recordEvent (D := D) Ω zero record) positive).probability event ≤
        (G.repetition (Fintype.card (CleanIndices Ω record))).value := by
  apply conditioned_source_success
    (childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected)
    (recordEvent (D := D) Ω zero record) event positive G
    (fun x (i : CleanIndices Ω record) => (x i.1).1) _ strategy inclusion
  exact clean_source_law Ω (fun _ => G.occurrences) ν flag nonprojected zero
    cardinality same_cardinality record positive

omit [∀ index, DecidableEq (D index)] in
theorem source_soundness_oai
    (G : OccurrenceGame E Q₁ Q₂ A₁ A₂)
    (ν : (i : I) → FiniteDistribution (R i))
    (flag : (i : I) → FiniteDistribution Bool)
    (nonprojected : (i : I) → E × R i → FiniteDistribution (D i))
    (zero : (i : I) → (s : E × R i) → (j : J i) → Ω i s j)
    (cardinality : (i : I) → J i → Nat)
    (same_cardinality : ∀ i s j, Fintype.card (Ω i s j) = cardinality i j)
    (event : Sample (D := D) Ω → Bool) (a : ℝ)
    (repetition : ∀ n, (G.repetition n).value ≤ a ^ n)
    (strategies : (record : FullRecord (D := D) Ω) →
      Strategy (CleanIndices Ω record → Q₁) (CleanIndices Ω record → Q₂)
        (CleanIndices Ω record → A₁) (CleanIndices Ω record → A₂))
    (inclusion : ∀ record x, recordEvent (D := D) Ω zero record x = true → event x = true →
      (IndexedRepetition.game G (CleanIndices Ω record)).wins (strategies record)
        (fun i => (x i.1).1) = true) :
    (childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected).probability event ≤
      ∏ i : I, (1 - (1 - a) *
        ((flag i).weight true * ∏ j : J i, 1 / (cardinality i j : ℝ))) := by
  classical
  let P := fun i => kernelJoint G.occurrences (fun e =>
    kernelJoint (ν i) (childKernel Ω flag nonprojected i e))
  let clean := fun i (y : E × (R i × ChildRaw (D := D) Ω i)) =>
    childClean (D := D) Ω zero i y.1 y.2.1 y.2.2
  have conditional : ∀ record (positive : 0 < (law P).probability
      (fun x => decide (observations (D := D) Ω zero x = record))),
      ((law P).condition (fun x => decide (observations (D := D) Ω zero x = record))
        positive).probability event ≤ a ^ Fintype.card (CleanIndices Ω record) := by
    intro record positive
    have hp' : 0 < (childrenLaw Ω (fun _ => G.occurrences) ν flag nonprojected).probability
        (recordEvent (D := D) Ω zero record) := by
      simpa only [childrenLaw, P, recordEvent_eq] using positive
    have bound := (conditional_source_bound Ω G ν flag nonprojected zero cardinality
      same_cardinality record hp' event (strategies record) (inclusion record)).trans
        (repetition _)
    simpa only [childrenLaw, P, recordEvent_eq] using bound
  have h := independent_clean_bound P clean (observations (D := D) Ω zero)
    (fun record => Fintype.card (CleanIndices Ω record))
    (observed_clean_count Ω zero) event a conditional
  have hp (i : I) : (P i).probability (clean i) =
      (flag i).weight true * ∏ j : J i, 1 / (cardinality i j : ℝ) := by
    apply CleanCounting.kernel_clean_probability
      (fun _ => G.occurrences) ν (childKernel Ω flag nonprojected)
      (childClean (D := D) Ω zero)
      (fun i => (flag i).weight true * ∏ j : J i, 1 / (cardinality i j : ℝ)) _ i
    intro k e r
    exact probability_projectedKernel_zero_constant (Ω k) (flag k) (nonprojected k)
      (zero k) (cardinality k) (same_cardinality k) (e, r)
  change (law P).probability event ≤ _
  simpa only [hp] using h

end
end PerfectCompleteness.UniformCleanSoundness



end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9, u_10} : type_of% @OAI.PerfectCompleteness.UniformCleanSoundness.source_soundness_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9, u_10} := @OAI.PerfectCompleteness.UniformCleanSoundness.source_soundness_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8, u_9, u_10}
