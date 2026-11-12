-- Prove2me | solution 1 for OAI.PerfectCompleteness.UpperScalarPairAveraging.fixed_pairLaw
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:28:19.222961+00:00
-- url     : https://prove2.me/submissions/3d5560c2-aafa-4737-841e-e9832552bcd9

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
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.LinearMap.End
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
import Mathlib.Algebra.Polynomial.Inductions
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
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Finite.Basic
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
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
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
import Definitions.Def_OAIQ252P020

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
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

end FiniteDistribution

end UniqueGamesTheorem.Foundations.Games

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_KernelSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators
noncomputable section

namespace FiniteDistribution

/-- Applying separate maps to independent samples preserves their independence. -/
theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

theorem transport_eq_pushforward (μ : FiniteDistribution A) (e : A ≃ B) :
    μ.transport e = μ.pushforward e := by
  classical
  apply eq_of_weight_eq
  intro b
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton,
    probability_transport, probability_pushforward]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RationalFiniteLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

namespace PerfectCompleteness.FiniteProduct

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω Γ : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Γ i)]

theorem pushforward_map (P : (i : I) → FiniteDistribution (Ω i))
    (f : (i : I) → Ω i → Γ i) :
    (law P).pushforward (fun x i => f i (x i)) =
      law (fun i => (P i).pushforward (f i)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  simp only [FiniteDistribution.pushforward, law]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArraySampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArraySampler

open TreeSourceSpaces HierarchicalArrays DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem components_expectation_product (rows repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (k : StepIndex i) → StepFactor (RootTape rows repeats (.step i p) slots)
      (Tape rows repeats p (childSlots slots i))
      (fun j => Arrays (childSlots slots j.val) rows) k → ℝ) :
    (tapeLaw rows repeats (.step i p) slots).expectation (fun ω => ∏ k, f k (ω k)) =
      ∏ k, (componentLaw rows repeats i p slots k).expectation (f k) := by
  let : (k : StepIndex i) → Fintype
      (StepFactor (RootTape rows repeats (.step i p) slots)
        (Tape rows repeats p (childSlots slots i))
        (fun j => Arrays (childSlots slots j.val) rows) k) :=
    fun k => stepFactorFintype _ _ _ k
  exact FiniteProduct.expectation_product (componentLaw rows repeats i p slots) f

end

end PerfectCompleteness.WholeArraySampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeArraySubtreeSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArraySubtreeSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

theorem rootTapeLaw_eq_uniform (rows repeats : Nat → Nat) (p : Path branch n m)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    BucketSampler.recursiveTapeLaw (rows n) repeats p (LeafDomain slots) =
      FiniteDistribution.uniform (RootTape rows repeats p slots) := by
  change FiniteProduct.law (fun _ : BucketSampler.Direction (rows n) =>
    RecursiveSampler.tapeLaw F2 repeats p (LeafDomain slots)) = _
  simp only [RecursiveSampler.tapeLaw_eq_uniform]
  exact UniformLinearImage.law_uniform

local instance stepFactorNonempty {i : Fin (branch n)} (Root Selected : Type)
    (Ordinary : RecursiveSampler.OffPath i → Type)
    [Nonempty Root] [Nonempty Selected] [∀ j, Nonempty (Ordinary j)]
    (field : StepIndex i) : Nonempty (StepFactor Root Selected Ordinary field) := by
  rcases field with _ | (_ | j) <;> dsimp only [StepFactor] <;> infer_instance

theorem tapeLaw_eq_uniform (rows repeats : Nat → Nat) (p : Path branch n m) :
    ∀ slots : Slots branch n → Fin t → MixedSupport.Slot,
      WholeArraySampler.tapeLaw rows repeats p slots =
        FiniteDistribution.uniform (Tape rows repeats p slots) := by
  induction p with
  | refl n => intro slots; rfl
  | @step n m i p ih =>
      intro slots
      let : (field : StepIndex i) → Fintype
          (StepFactor (RootTape rows repeats (.step i p) slots)
            (Tape rows repeats p (childSlots slots i))
            (fun j => Arrays (childSlots slots j.val) rows) field) :=
        fun field => stepFactorFintype _ _ _ field
      have hcomponent : componentLaw rows repeats i p slots =
          (fun field : StepIndex i => FiniteDistribution.uniform
            (StepFactor (RootTape rows repeats (.step i p) slots)
              (Tape rows repeats p (childSlots slots i))
              (fun j => Arrays (childSlots slots j.val) rows) field)) := by
        funext field
        rcases field with u | (u | j)
        · cases u
          exact rootTapeLaw_eq_uniform rows repeats (.step i p) slots
        · cases u
          exact ih (childSlots slots i)
        · rfl
      change FiniteProduct.law (componentLaw rows repeats i p slots) = _
      rw [hcomponent]
      exact UniformLinearImage.law_uniform

end
end PerfectCompleteness.WholeArraySubtreeSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuarterBalanceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.SourceCoordinateSplit

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem coordinate_split (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (law P).transport (Equiv.piSplitAt i Ω) =
      (P i).product (law (fun j : {j : I // j ≠ i} => P j)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∏ j, (P j).weight ((Equiv.piSplitAt i Ω).symm y j)) =
    (P i).weight y.1 * ∏ j : {j : I // j ≠ i}, (P j).weight (y.2 j)
  calc
    _ = ∏ j, if h : j = i then (P i).weight y.1 else (P j).weight (y.2 ⟨j, h⟩) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt, hj]
    _ = _ := by
      rw [Fintype.prod_dite]
      simp

theorem coordinate_split_pushforward (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) :
    (law P).pushforward (fun x => (x i, fun j : {j : I // j ≠ i} => x j)) =
      (P i).product (law (fun j : {j : I // j ≠ i} => P j)) := by
  change (law P).pushforward (Equiv.piSplitAt i Ω) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact coordinate_split P i

end
end PerfectCompleteness.SourceCoordinateSplit



namespace PerfectCompleteness.FiniteProductSplit

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem split_law (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (FiniteProduct.law P).pushforward (Equiv.piSplitAt i Ω) =
      (P i).product (otherLaw P i) :=
  SourceCoordinateSplit.coordinate_split_pushforward P i

end
end PerfectCompleteness.FiniteProductSplit

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SamplerComposition
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SamplerComposition

open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}

theorem evaluate_collapseExpanded (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (t : ExpandedTape 𝕜 repeats p q A),
      RecursiveSampler.evaluate 𝕜 repeats p A (collapseExpanded 𝕜 repeats p q A t) =
        RecursiveSampler.evaluate 𝕜 repeats (p.append q) A (flatten 𝕜 repeats p q A t) := by
  induction p with
  | refl n => intro q A t; rfl
  | @step n m i p ih =>
      intro q A t
      have hl := funext fun h : Fin (repeats (n + 1)) =>
        ih q (childFamily A i) (expandedSubTape 𝕜 repeats i p q A t h false)
      have hr := funext fun h : Fin (repeats (n + 1)) =>
        ih q (childFamily A i) (expandedSubTape 𝕜 repeats i p q A t h true)
      exact congrArg₂
        (fun (left right : Fin (repeats (n + 1)) → space 𝕜 branch n (childFamily A i)) =>
          combine 𝕜 A i (repeats (n + 1)) (fun j => t (.inl j)) left right) hl hr

theorem evaluate_collapseSuffix (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u)
    (t : RecursiveSampler.Tape 𝕜 repeats (p.append q) A) :
    RecursiveSampler.evaluate 𝕜 repeats p A (collapseSuffix 𝕜 repeats p q A t) =
      RecursiveSampler.evaluate 𝕜 repeats (p.append q) A t :=
  (evaluate_collapseExpanded 𝕜 repeats p q A (expand 𝕜 repeats p q A t)).trans
    (congrArg (RecursiveSampler.evaluate 𝕜 repeats (p.append q) A)
      (flatten_expand 𝕜 repeats p q A t))

end
end PerfectCompleteness.SamplerComposition

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalTerminalSplitLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalTerminalSplit

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls SamplerComposition
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}

variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (q : Path branch m k) (A : Slots branch n → Type u)

variable [Finite 𝕜] [hA : ∀ s, Finite (A s)]

local instance familyFinite_r32eec7_1 : ∀ s, Finite (p.family A s) :=
  fun s => hA (p.slotEmbedding s)
theorem terminalLaw_uniform :
    terminalLaw 𝕜 repeats p q A = FiniteDistribution.uniform (TerminalTape 𝕜 repeats p q A) := by
  simp only [terminalLaw, RecursiveSampler.tapeLaw_eq_uniform, UniformLinearImage.law_uniform]

theorem exteriorLaw_uniform :
    exteriorLaw 𝕜 repeats p A = FiniteDistribution.uniform (ExteriorTape 𝕜 repeats p A) :=
  UniformLinearImage.law_uniform

theorem split_tapeLaw :
    (RecursiveSampler.tapeLaw 𝕜 repeats (p.append q) A).pushforward
      (splitTape 𝕜 repeats p q A) =
        (terminalLaw 𝕜 repeats p q A).product (exteriorLaw 𝕜 repeats p A) := by
  rw [RecursiveSampler.tapeLaw_eq_uniform, FiniteDistribution.pushforward_equiv,
    terminalLaw_uniform, exteriorLaw_uniform]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (RecursiveSampler.Tape 𝕜 repeats (p.append q) A) : ℝ) =
    (1 / (Fintype.card (TerminalTape 𝕜 repeats p q A) : ℝ)) *
      (1 / (Fintype.card (ExteriorTape 𝕜 repeats p A) : ℝ))
  rw [Fintype.card_congr (splitTape 𝕜 repeats p q A), Fintype.card_prod]
  simp only [Nat.cast_mul, one_div, mul_inv]

end
end PerfectCompleteness.OriginalTerminalSplit

end

section

namespace PerfectCompleteness.OriginalScalarReconstruction

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls SamplerComposition
open OriginalTerminalSplit
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m k : Nat}
variable (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (p : Path branch n m) (A : Slots branch n → Type u)

theorem collapseFactor_terminal :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (terminal : TerminalIndex repeats p)
      (x : ExpansionSpace 𝕜 repeats p q A (drawIndex repeats p terminal)),
      terminalSpaceEquiv 𝕜 repeats p A terminal
        (collapseFactor 𝕜 repeats p q A (drawIndex repeats p terminal) x) =
      RecursiveSampler.evaluate 𝕜 repeats q (p.family A)
        (terminalFactorEquiv 𝕜 repeats p q A terminal x) := by
  induction p with
  | refl n => intro q A terminal x; rfl
  | step i p ih =>
      intro q A terminal x
      exact ih q (childFamily A i) terminal.2 x

theorem collapseFactor_exterior :
    ∀ (q : Path branch m k) (A : Slots branch n → Type u)
      (j : DrawIndex repeats p) (hj : ¬ IsTerminal repeats p j)
      (x : ExpansionSpace 𝕜 repeats p q A j),
      collapseFactor 𝕜 repeats p q A j x =
        exteriorFactorEquiv 𝕜 repeats p q A ⟨j, hj⟩ x := by
  induction p with
  | refl n =>
      intro q A j hj x
      exact False.elim (hj True.intro)
  | step i p ih =>
      intro q A j hj x
      cases j with
      | inl j => rfl
      | inr j => exact ih q (childFamily A i) j.2 hj x

theorem prefixSplit_collapseExpanded (q : Path branch m k)
    (x : ExpandedTape 𝕜 repeats p q A) :
    prefixSplit 𝕜 repeats p A (collapseExpanded 𝕜 repeats p q A x) =
      (fun terminal => RecursiveSampler.evaluate 𝕜 repeats q (p.family A)
        ((splitExpanded 𝕜 repeats p q A x).1 terminal),
        (splitExpanded 𝕜 repeats p q A x).2) := by
  apply Prod.ext
  · funext terminal
    exact collapseFactor_terminal 𝕜 repeats p q A terminal (x (drawIndex repeats p terminal))
  · funext j
    exact collapseFactor_exterior 𝕜 repeats p q A j.val j.property (x j.val)

theorem reconstruct_original (q : Path branch m k)
    (x : RecursiveSampler.Tape 𝕜 repeats (p.append q) A) :
    reconstruct 𝕜 repeats p A
      (fun terminal => RecursiveSampler.evaluate 𝕜 repeats q (p.family A)
        ((splitTape 𝕜 repeats p q A x).1 terminal))
      (splitTape 𝕜 repeats p q A x).2 =
        RecursiveSampler.evaluate 𝕜 repeats (p.append q) A x := by
  have hsplit := prefixSplit_collapseExpanded 𝕜 repeats p A q
    (expandEquiv 𝕜 repeats p q A x)
  change prefixSplit 𝕜 repeats p A (collapseSuffix 𝕜 repeats p q A x) =
    (fun terminal => RecursiveSampler.evaluate 𝕜 repeats q (p.family A)
      ((splitTape 𝕜 repeats p q A x).1 terminal),
      (splitTape 𝕜 repeats p q A x).2) at hsplit
  unfold reconstruct
  rw [← hsplit, Equiv.symm_apply_apply]
  exact evaluate_collapseSuffix 𝕜 repeats p q A x

end
end PerfectCompleteness.OriginalScalarReconstruction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutCallsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.OriginalCutCalls

open RecursiveSpaces DescendantSpaces TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

theorem ownBucket_injective (rows repeats : Nat → Nat) (p : Path branch n m) :
    Function.Injective (ownBucket rows repeats p) := by
  induction p with
  | refl m => exact fun _ _ h => h
  | step i p ih =>
      intro a b h
      exact ih (Sum.inr.inj h)

end
end PerfectCompleteness.OriginalCutCalls

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OriginalWholeCutTape
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutTape

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

theorem callsLaw_uniform (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    callsLaw rows repeats p chosen q slots =
      FiniteDistribution.uniform (Calls rows repeats p chosen q slots) := by
  simp only [callsLaw, RecursiveSampler.tapeLaw_eq_uniform, UniformLinearImage.law_uniform]

theorem belowLaw_uniform (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    belowLaw rows repeats chosen q slots =
      FiniteDistribution.uniform (BelowTape rows repeats chosen q slots) := by
  rw [belowLaw, WholeArraySubtreeSplit.tapeLaw_eq_uniform, UniformLinearImage.law_uniform]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

theorem split_tapeLaw (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
        (splitTape rows repeats p chosen q slots) =
      (exteriorLaw rows repeats p slots).product
        ((callsLaw rows repeats p chosen q slots).product
          (belowLaw rows repeats chosen q (cutSlots p slots))) := by
  rw [WholeArraySubtreeSplit.tapeLaw_eq_uniform, FiniteDistribution.pushforward_equiv,
    callsLaw_uniform, belowLaw_uniform]
  unfold exteriorLaw
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card
      (WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots) : ℝ) =
    (1 / (Fintype.card (Exterior rows repeats p slots) : ℝ)) *
      ((1 / (Fintype.card (Calls rows repeats p chosen q slots) : ℝ)) *
        (1 / (Fintype.card (BelowTape rows repeats chosen q (cutSlots p slots)) : ℝ)))
  rw [Fintype.card_congr (splitTape rows repeats p chosen q slots),
    Fintype.card_prod, Fintype.card_prod]
  simp only [Nat.cast_mul, one_div, mul_inv]

end

end PerfectCompleteness.OriginalWholeCutTape

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutNodeRows
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutNodeRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {N cut t : Nat}

theorem native_selectedRows (rows : Nat → Nat) :
    {N cut : Nat} → (p : Path branch N (cut + 1)) →
      (slots : Slots branch N → Fin t → MixedSupport.Slot) → (arrays : Arrays slots rows) →
      (fun i => nativeEquiv p slots
        (SelectedArrayReplacement.selectedRows rows p slots arrays ((rowIndexEquiv rows p).symm i))) =
        arrays (upperNode p)
  | _, _, .refl _, _, _ => rfl
  | _, _, .step i p, slots, arrays =>
      native_selectedRows rows p (childSlots slots i) (fun node => arrays (.inr (i, node)))

theorem transportRows_selectedRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    transportRows rows p slots (SelectedArrayReplacement.selectedRows rows p slots arrays) =
      NodeEmbedding.embeddedRows arrays (upperNode p) := by
  funext i
  exact congrArg (NodeEmbedding.embed slots (upperNode p))
    (congrFun (native_selectedRows rows p slots arrays) i)

theorem ofRows_selectedRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots (upperNode p))
        (transportRows rows p slots (SelectedArrayReplacement.selectedRows rows p slots arrays)) =
      NodeEmbedding.matrix arrays (upperNode p) := by
  rw [transportRows_selectedRows]
  rfl

theorem matrixOfRows_selectedRows (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows) :
    matrixOfRows rows p slots (SelectedArrayReplacement.selectedRows rows p slots arrays) =
      NodeEmbedding.matrix arrays (upperNode p) :=
  ofRows_selectedRows rows p slots arrays

private theorem tape_equiv_update {V W : Type*} {ℓ ℓ' : Nat} (h : ℓ = ℓ')
    (e : V ≃ W) (tape : BucketSampler.Tape ℓ V) (a : BucketSampler.Direction ℓ) (fresh : V) :
    Equiv.arrowCongr (Equiv.cast (congrArg BucketSampler.Direction h)) e
        (Function.update tape a fresh) =
      Function.update
        (Equiv.arrowCongr (Equiv.cast (congrArg BucketSampler.Direction h)) e tape)
        (Equiv.cast (congrArg BucketSampler.Direction h) a) (e fresh) := by
  cases h
  funext d
  change e (Function.update tape a fresh d) =
    Function.update (fun v => e (tape v)) a (e fresh) d
  exact Function.apply_update (fun (_ : BucketSampler.Direction ℓ) (v : V) => e v)
    tape a fresh d

theorem bucketTapeEquiv_update (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots)))
    (a : BucketSampler.Direction (rows (cut + 1))) (fresh : H (cutSlots p slots)) :
    bucketTapeEquiv rows p slots (Function.update tape a fresh) =
      Function.update (bucketTapeEquiv rows p slots tape)
        (directionEquiv rows p a) (cutRowEquiv p slots fresh) :=
  tape_equiv_update (congrArg rows (upperNode_height p)).symm
    (cutRowEquiv p slots).toEquiv tape a fresh

private theorem evaluate_equiv {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    [Module F2 V] [Module F2 W] {ℓ ℓ' : Nat} (h : ℓ = ℓ')
    (e : V ≃ₗ[F2] W) (tape : BucketSampler.Tape ℓ V) :
    (fun i => e (BucketSampler.evaluate ℓ (id : V → V) tape
        ((Equiv.cast (congrArg Fin h)).symm i))) =
      BucketSampler.evaluate ℓ' (id : W → W)
        (Equiv.arrowCongr (Equiv.cast (congrArg BucketSampler.Direction h)) e.toEquiv tape) := by
  cases h
  funext i
  change e (∑ v : BucketSampler.Direction ℓ, v.val i • tape v) =
    ∑ v : BucketSampler.Direction ℓ, v.val i • e (tape v)
  simp only [map_sum, map_smul]

theorem transportRows_evaluate (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots))) :
    transportRows rows p slots
        (BucketSampler.evaluate (rows (cut + 1)) (id : H (cutSlots p slots) → _) tape) =
      BucketSampler.evaluate (rows (Nodes.height (upperNode p)))
        (id : NodeEmbedding.RowSpace slots (upperNode p) → _) (bucketTapeEquiv rows p slots tape) :=
  evaluate_equiv (congrArg rows (upperNode_height p)).symm (cutRowEquiv p slots) tape

theorem matrixOfRows_evaluate (rows : Nat → Nat) (p : Path branch N (cut + 1))
    (slots : Slots branch N → Fin t → MixedSupport.Slot)
    (tape : BucketSampler.Tape (rows (cut + 1)) (H (cutSlots p slots))) :
    matrixOfRows rows p slots
        (BucketSampler.evaluate (rows (cut + 1)) (id : H (cutSlots p slots) → _) tape) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p))) (bucketTapeEquiv rows p slots tape) := by
  unfold matrixOfRows BucketMatrixResampling.assembledMatrix
  rw [transportRows_evaluate]

end
end PerfectCompleteness.CutNodeRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildBlockProducts
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalChildBlockProducts

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

universe uC uI uΩ uΓ uΔ

theorem merge_law {I : Type uI} [Fintype I] [DecidableEq I]
    {Ω : I → Type uΩ} [∀ i, Fintype (Ω i)]
    (P : (i : I) → FiniteDistribution (Ω i)) (chosen : I) :
    ((P chosen).product (FiniteProductSplit.otherLaw P chosen)).pushforward
        (Equiv.piSplitAt chosen Ω).symm =
      FiniteProduct.law P := by
  rw [← FiniteProductSplit.split_law P chosen, FiniteDistribution.pushforward_comp]
  have hmap : (fun x => (Equiv.piSplitAt chosen Ω).symm
      ((Equiv.piSplitAt chosen Ω) x)) = id := by
    funext x
    exact (Equiv.piSplitAt chosen Ω).symm_apply_apply x
  rw [hmap, FiniteDistribution.pushforward_id]

end
end PerfectCompleteness.OriginalChildBlockProducts

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

theorem reconstructBuckets_original (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (r : Path branch (m + 1) k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ω : WholeArraySampler.RootTape rows repeats (p.append r) slots) :
    reconstructBuckets rows repeats p slots
        (fun direction terminal => RecursiveSampler.evaluate F2 repeats r
          (p.family (LeafDomain slots))
          ((OriginalTerminalSplit.splitTape F2 repeats p r (LeafDomain slots)
            (ω direction)).1 terminal))
        (fun direction => (OriginalTerminalSplit.splitTape F2 repeats p r (LeafDomain slots)
          (ω direction)).2) =
      BucketSampler.recursiveEvaluate (rows n) repeats (p.append r) (LeafDomain slots) ω := by
  have h := funext (fun direction : BucketSampler.Direction (rows n) =>
    OriginalScalarReconstruction.reconstruct_original F2 repeats p (LeafDomain slots) r
      (ω direction))
  exact congrArg (BucketSampler.evaluate (rows n) (id : H slots → H slots)) h

theorem reconstruct_original (rows repeats : Nat → Nat) :
    ∀ {n m k : Nat} (p : Path branch n (m + 1)) (chosen : Fin (branch m))
      (q : Path branch m k) (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (ω : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots),
      reconstructRecord rows repeats p slots (readRecord rows repeats p chosen q slots ω) =
        WholeArraySampler.evaluate rows repeats (p.append (.step chosen q)) slots ω := by
  intro n
  induction n with
  | zero =>
      intro m k p
      cases p
  | succ n ih =>
      intro m k p chosen q slots ω
      cases p with
      | refl => rfl
      | step i p =>
          exact congrArg₂ (WholeArraySampler.assemble slots rows)
            (reconstructBuckets_original rows repeats (.step i p) (.step chosen q) slots
              (ω (.inl ())))
            (congrArg (fun selected : Arrays (childSlots slots i) rows =>
              WholeArraySampler.childrenAt slots rows i selected (fun j => ω (.inr (.inr j))))
              (ih p chosen q (childSlots slots i) (ω (.inr (.inl ())))))

end
end PerfectCompleteness.OriginalWholeCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalCutBucketReplacement
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutBucketReplacement

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut OriginalWholeCutTape
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem ownValues_replaceValues (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (values : Values rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (fresh : H (cutSlots p slots)) :
    ownValues rows repeats p slots (replaceValues rows repeats p slots values a fresh) =
      Function.update (ownValues rows repeats p slots values) a fresh :=
  Function.update_comp_eq_of_injective' values
    (OriginalCutCalls.ownBucket_injective rows repeats p) a fresh

theorem selectedRows_reconstruct (rows repeats : Nat → Nat) :
    ∀ {n m : Nat} (p : Path branch n (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats p slots) (values : Values rows repeats p slots)
      (below : BelowArrays rows p slots),
      SelectedArrayReplacement.selectedRows rows p slots
          (reconstruct rows repeats p slots exterior values below) =
        BucketSampler.evaluate (rows (m + 1)) (id : H (cutSlots p slots) → H (cutSlots p slots))
          (ownValues rows repeats p slots values) := by
  intro n
  induction n with
  | zero => intro m p; cases p
  | succ n ih =>
      intro m p slots exterior values below
      cases p with
      | refl => rfl
      | step i p =>
          change SelectedArrayReplacement.selectedRows rows (.step i p) slots
            (WholeArraySampler.assemble slots rows
              (reconstructBuckets rows repeats (.step i p) slots
                (fun direction terminal => values (.inl (direction, terminal))) exterior.1)
              (WholeArraySampler.childrenAt slots rows i
                (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                  (fun call => values (.inr call)) below) exterior.2.2)) = _
          rw [SelectedArrayReplacement.selectedRows_assemble_step]
          exact ih p (childSlots slots i) exterior.2.1 (fun call => values (.inr call)) below

end
end PerfectCompleteness.OriginalCutBucketReplacement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeArrayProductLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayProductLaw

open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem prod_stepIndex (i : Fin (branch n)) (f : StepIndex i → ℝ) :
    (∏ k, f k) = f (.inl ()) *
      (f (.inr (.inl ())) * ∏ j : RecursiveSampler.OffPath i, f (.inr (.inr j))) := by
  change (∏ k : Unit ⊕ (Unit ⊕ RecursiveSampler.OffPath i), f k) = _
  simp only [Fintype.prod_sum_type, Fintype.prod_unique]

theorem eq_law_of_expectation_product {I : Type*} [Fintype I] [DecidableEq I]
    {Ω : I → Type*} [∀ i, Fintype (Ω i)]
    (μ : FiniteDistribution (∀ i, Ω i)) (P : ∀ i, FiniteDistribution (Ω i))
    (h : ∀ f : ∀ i, Ω i → ℝ,
      μ.expectation (fun x => ∏ i, f i (x i)) = ∏ i, (P i).expectation (f i)) :
    μ = FiniteProduct.law P := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  calc
    μ.weight y = μ.expectation (fun x => if x = y then 1 else 0) := by
      simp [FiniteDistribution.expectation, mul_ite]
    _ = μ.expectation (fun x => ∏ i, if x i = y i then 1 else 0) := by
      apply FiniteDistribution.expectation_congr
      intro x
      simp only [Fintype.prod_boole, funext_iff]
    _ = ∏ i, (P i).expectation (fun a => if a = y i then 1 else 0) :=
      h (fun i a => if a = y i then (1 : ℝ) else 0)
    _ = (FiniteProduct.law P).weight y := by
      simp [FiniteProduct.law, FiniteDistribution.expectation, mul_ite]

end

end PerfectCompleteness.WholeArrayProductLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalBelowCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalBelowCut

open TreeSourceSpaces HierarchicalArrays DescendantSpaces WholeArraySampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem prod_below (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (child : Fin (branch n)) → Arrays (childSlots slots child) rows → ℝ)
    (ω : Tape rows repeats (.step chosen q) slots) :
    (∏ child, f child (below rows repeats chosen q slots ω child)) =
      ∏ k : StepIndex chosen, stepObservable rows repeats chosen q slots f k (ω k) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne
    (fun child => f child (below rows repeats chosen q slots ω child)) chosen,
    WholeArrayProductLaw.prod_stepIndex chosen]
  simp only [stepObservable, one_mul, below_selected, below_ordinary]

theorem expectation_product (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (f : (child : Fin (branch n)) → Arrays (childSlots slots child) rows → ℝ) :
    (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots).expectation
        (fun ω => ∏ child, f child (below rows repeats chosen q slots ω child)) =
      ∏ child, (ChildBlockMixture.component
        (fun j => WholeArraySampler.law rows repeats q (childSlots slots j))
        chosen child).expectation (f child) := by
  calc
    _ = (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots).expectation
        (fun ω => ∏ k : StepIndex chosen,
          stepObservable rows repeats chosen q slots f k (ω k)) :=
      FiniteDistribution.expectation_congr _ (prod_below rows repeats chosen q slots f)
    _ = ∏ k : StepIndex chosen, (componentLaw rows repeats chosen q slots k).expectation
        (stepObservable rows repeats chosen q slots f k) :=
      WholeArraySampler.components_expectation_product rows repeats chosen q slots _
    _ = _ := by
      let Q : (child : Fin (branch n)) →
          FiniteDistribution (Arrays (childSlots slots child) rows) :=
        fun child => WholeArraySampler.law rows repeats q (childSlots slots child)
      let L : StepIndex chosen → ℝ := fun k =>
        (componentLaw rows repeats chosen q slots k).expectation
          (stepObservable rows repeats chosen q slots f k)
      let R : Fin (branch n) → ℝ := fun child =>
        (ChildBlockMixture.component Q chosen child).expectation (f child)
      change (∏ k, L k) = ∏ child, R child
      have hroot : L (.inl ()) = 1 :=
        SmallBias.expectation_const _ 1
      have hselected : L (.inr (.inl ())) = R chosen := by
        change (WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen)).expectation
          (fun ω => f chosen (WholeArraySampler.evaluate rows repeats q
            (childSlots slots chosen) ω)) =
          (ChildBlockMixture.component Q chosen chosen).expectation (f chosen)
        simp only [ChildBlockMixture.component]
        exact (FiniteDistribution.expectation_pushforward
          (WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen))
          (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen))
          (f chosen)).symm
      have hordinary (j : RecursiveSampler.OffPath chosen) :
          L (.inr (.inr j)) = R j.val := by
        change (FiniteDistribution.uniform (Arrays (childSlots slots j.val) rows)).expectation
          (f j.val) = (ChildBlockMixture.component Q chosen j.val).expectation (f j.val)
        simp only [ChildBlockMixture.component, dite_eq_right (Ne.symm j.property)]
      rw [WholeArrayProductLaw.prod_stepIndex chosen, hroot, one_mul, hselected,
        Fintype.prod_eq_mul_prod_subtype_ne R chosen]
      exact congrArg (fun z : ℝ => R chosen * z)
        (Finset.prod_congr rfl (fun j _ => hordinary j))

theorem below_pushforward (rows repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m)
    (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots).pushforward
        (below rows repeats chosen q slots) =
      FiniteProduct.law (ChildBlockMixture.component
        (fun child => WholeArraySampler.law rows repeats q (childSlots slots child)) chosen) := by
  apply WholeArrayProductLaw.eq_law_of_expectation_product
  intro f
  rw [FiniteDistribution.expectation_pushforward]
  exact expectation_product rows repeats chosen q slots f

end

end PerfectCompleteness.OriginalBelowCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalWholeCutLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedStoppedDecoderContext.upper_height _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerNode_height _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem product_map_record {E A B V D : Type*}
    [Fintype E] [Fintype A] [Fintype B] [Fintype V] [Fintype D]
    (exterior : FiniteDistribution E) (calls : FiniteDistribution A)
    (below : FiniteDistribution B) (values : A → V) (arrays : B → D) :
    (exterior.product (calls.product below)).pushforward
        (fun z => (z.1, (values z.2.1, arrays z.2.2))) =
      exterior.product ((calls.pushforward values).product (below.pushforward arrays)) := by
  calc
    _ = (exterior.pushforward id).product
        ((calls.product below).pushforward (fun z => (values z.1, arrays z.2))) :=
      FiniteDistribution.product_pushforward exterior (calls.product below) id
        (fun z => (values z.1, arrays z.2))
    _ = _ := by rw [FiniteDistribution.pushforward_id, FiniteDistribution.product_pushforward]

variable {branch : Nat → Nat} {n m k t : Nat}

attribute [local instance 2000] valuesBelowFintype

theorem childrenAt_law (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (chosen : Fin (branch m))
    (Q : (child : Fin (branch m)) →
      FiniteDistribution (Arrays (childSlots slots child) rows)) :
    ((Q chosen).product (FiniteProduct.law
        (fun child : RecursiveSampler.OffPath chosen =>
          FiniteDistribution.uniform (Arrays (childSlots slots child.val) rows)))).pushforward
        (fun z => WholeArraySampler.childrenAt slots rows chosen z.1 z.2) =
      FiniteProduct.law (ChildBlockMixture.component Q chosen) := by
  have hselected : ChildBlockMixture.component Q chosen chosen = Q chosen := dite_eq_left rfl
  have hother : FiniteProductSplit.otherLaw (ChildBlockMixture.component Q chosen) chosen =
      FiniteProduct.law (fun child : RecursiveSampler.OffPath chosen =>
        FiniteDistribution.uniform (Arrays (childSlots slots child.val) rows)) := by
    apply congrArg (fun laws : (child : RecursiveSampler.OffPath chosen) →
      FiniteDistribution (Arrays (childSlots slots child.val) rows) => FiniteProduct.law laws)
    funext child
    exact dite_eq_right (Ne.symm child.property)
  have h := OriginalChildBlockProducts.merge_law (ChildBlockMixture.component Q chosen) chosen
  rw [hselected, hother] at h
  exact h

theorem below_product_law (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    ((WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen)).product
        (FiniteProduct.law (fun child : RecursiveSampler.OffPath chosen =>
          FiniteDistribution.uniform (Arrays (childSlots slots child.val) rows)))).pushforward
        (fun z => WholeArraySampler.childrenAt slots rows chosen
          (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen) z.1) z.2) =
      belowArraysLaw rows repeats chosen q slots := by
  let ordinary := FiniteProduct.law (fun child : RecursiveSampler.OffPath chosen =>
    FiniteDistribution.uniform (Arrays (childSlots slots child.val) rows))
  calc
    _ = (((WholeArraySampler.tapeLaw rows repeats q (childSlots slots chosen)).product
        ordinary).pushforward (fun z =>
          (WholeArraySampler.evaluate rows repeats q (childSlots slots chosen) z.1,
            z.2))).pushforward
              (fun z => WholeArraySampler.childrenAt slots rows chosen z.1 z.2) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((WholeArraySampler.law rows repeats q (childSlots slots chosen)).product
        ordinary).pushforward
          (fun z => WholeArraySampler.childrenAt slots rows chosen z.1 z.2) := by
      apply congrArg (fun μ : FiniteDistribution
          (Arrays (childSlots slots chosen) rows ×
            ((child : RecursiveSampler.OffPath chosen) →
              Arrays (childSlots slots child.val) rows)) =>
        μ.pushforward (fun z => WholeArraySampler.childrenAt slots rows chosen z.1 z.2))
      apply FiniteDistribution.eq_of_weight_eq
      rintro ⟨a, b⟩
      simp only [WholeArraySampler.law, FiniteDistribution.pushforward,
        FiniteDistribution.product]
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      by_cases h : WholeArraySampler.evaluate rows repeats q
        (childSlots slots chosen) ω = a <;> simp [h]
    _ = _ := childrenAt_law rows slots chosen
      (fun child => WholeArraySampler.law rows repeats q (childSlots slots child))

theorem belowEvaluate_law (rows repeats : Nat → Nat) (chosen : Fin (branch m))
    (q : Path branch m k) (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (OriginalWholeCutTape.belowLaw rows repeats chosen q slots).pushforward
        (OriginalWholeCut.belowEvaluate rows repeats chosen q slots) =
      belowArraysLaw rows repeats chosen q slots :=
  below_product_law rows repeats chosen q slots

theorem callsEvaluate_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalWholeCutTape.callsLaw rows repeats p chosen q slots).pushforward
        (fun calls call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
          (LeafDomain (OriginalWholeCutTape.cutSlots p slots)) (calls call)) =
      valuesLaw rows repeats p chosen q slots :=
  FiniteProduct.pushforward_map
    (fun _ : OriginalCutCalls.Index rows repeats p =>
      RecursiveSampler.tapeLaw F2 repeats (.step chosen q)
        (LeafDomain (OriginalWholeCutTape.cutSlots p slots)))
    (fun _ => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (OriginalWholeCutTape.cutSlots p slots)))

theorem readRecord_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
        (OriginalWholeCut.readRecord rows repeats p chosen q slots) =
      recordLaw rows repeats p chosen q slots := by
  let values : OriginalWholeCutTape.Calls rows repeats p chosen q slots →
      OriginalWholeCut.Values rows repeats p slots :=
    fun calls call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain (OriginalWholeCutTape.cutSlots p slots)) (calls call)
  let arrays : OriginalWholeCutTape.BelowTape rows repeats chosen q
      (OriginalWholeCutTape.cutSlots p slots) → OriginalWholeCut.BelowArrays rows p slots :=
    OriginalWholeCut.belowEvaluate rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots)
  let observe : OriginalWholeCutTape.Exterior rows repeats p slots ×
      (OriginalWholeCutTape.Calls rows repeats p chosen q slots ×
        OriginalWholeCutTape.BelowTape rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots)) →
      OriginalWholeCut.Record rows repeats p slots :=
    fun z => (z.1, (values z.2.1, arrays z.2.2))
  change (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).pushforward
    (fun ω => observe (OriginalWholeCutTape.splitTape rows repeats p chosen q slots ω)) = _
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots)
    (OriginalWholeCutTape.splitTape rows repeats p chosen q slots) observe,
    OriginalWholeCutTape.split_tapeLaw]
  apply Eq.trans (product_map_record
    (E := OriginalWholeCutTape.Exterior rows repeats p slots)
    (A := OriginalWholeCutTape.Calls rows repeats p chosen q slots)
    (B := OriginalWholeCutTape.BelowTape rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots))
    (V := OriginalWholeCut.Values rows repeats p slots)
    (D := OriginalWholeCut.BelowArrays rows p slots)
    (OriginalWholeCutTape.exteriorLaw rows repeats p slots)
    (OriginalWholeCutTape.callsLaw rows repeats p chosen q slots)
    (OriginalWholeCutTape.belowLaw rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots))
    values arrays)
  exact congrArg
    (fun μ : FiniteDistribution
        (OriginalWholeCut.Values rows repeats p slots × OriginalWholeCut.BelowArrays rows p slots) =>
      (OriginalWholeCutTape.exteriorLaw rows repeats p slots).product μ)
    (congrArg₂
      (fun (μ : FiniteDistribution (OriginalWholeCut.Values rows repeats p slots))
          (ν : FiniteDistribution (OriginalWholeCut.BelowArrays rows p slots)) => μ.product ν)
      (callsEvaluate_law rows repeats p chosen q slots)
      (belowEvaluate_law rows repeats chosen q (OriginalWholeCutTape.cutSlots p slots)))

end
end PerfectCompleteness.OriginalWholeCutLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCutBridge
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutBridge

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

private theorem pair_map_transport {A B C D Z : Type*}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype Z]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (f : A → C) (g : B → D) (e : C × D ≃ Z) :
    (μ.product ν).pushforward (fun x => e (f x.1, g x.2)) =
      ((μ.pushforward f).product (ν.pushforward g)).transport e := by
  rw [FiniteDistribution.transport_eq_pushforward]
  calc
    _ = ((μ.product ν).pushforward (fun x => (f x.1, g x.2))).pushforward e :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := congrArg (fun ρ : FiniteDistribution (C × D) => ρ.pushforward e)
      (FiniteDistribution.product_pushforward μ ν f g)

variable {branch : Nat → Nat} {n m k t : Nat}

theorem observed_product_law (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch m)) (q : Path branch m k)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (OriginalChildBlocks.sourceLaw calls rows repeats chosen q slots).pushforward
        (OriginalChildBlocks.observed calls rows repeats chosen q slots) =
      @FiniteDistribution.transport
        ((Fin calls → H slots) × ChildArrays rows slots)
        (CutChildGrouping.Assembled (C := Fin calls) slots rows)
        (instFintypeProd _ _) (CutChildGrouping.assembledFintype (C := Fin calls) slots rows)
        ((scalarValuesLaw calls repeats chosen q slots).product
          (belowArraysLaw rows repeats chosen q slots))
        (assembledEquiv calls rows slots) := by
  have hcalls : (OriginalChildScalars.callsLaw calls repeats chosen q slots).pushforward
      (fun tapes call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
        (LeafDomain slots) (tapes call)) = scalarValuesLaw calls repeats chosen q slots :=
    FiniteProduct.pushforward_map
      (fun _ : Fin calls => RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain slots))
      (fun _ => RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots))
  have hmap := pair_map_transport
    (A := Fin calls → OriginalChildScalars.ScalarTape repeats chosen q slots)
    (B := WholeArraySampler.Tape rows repeats (.step chosen q) slots)
    (C := Fin calls → H slots) (D := ChildArrays rows slots)
    (Z := CutChildGrouping.Assembled (C := Fin calls) slots rows)
    (OriginalChildScalars.callsLaw calls repeats chosen q slots)
    (WholeArraySampler.tapeLaw rows repeats (.step chosen q) slots)
    (fun tapes call => RecursiveSampler.evaluate F2 repeats (.step chosen q)
      (LeafDomain slots) (tapes call))
    (OriginalBelowCut.below rows repeats chosen q slots)
    (assembledEquiv calls rows slots)
  rw [hcalls, OriginalBelowCut.below_pushforward] at hmap
  exact hmap

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

end
end PerfectCompleteness.OriginalWholeCutBridge

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutReconstructionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutReconstruction

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

theorem reconstructFresh_readFresh (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : RecursiveSampler.Tape F2 repeats (r.append suffix) (LeafDomain (cutSlots p slots))) :
    reconstructFresh repeats p r slots (readFresh repeats p r suffix slots tape) =
      RecursiveSampler.evaluate F2 repeats (r.append suffix) (LeafDomain (cutSlots p slots)) tape := by
  simpa only [reconstructFresh, readFresh, Equiv.apply_symm_apply] using
    OriginalScalarReconstruction.reconstruct_original F2 repeats r
      (LeafDomain (cutSlots p slots)) suffix tape

end
end PerfectCompleteness.UpperScalarCutReconstruction

end

section

namespace PerfectCompleteness.UpperScalarCutBucket

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

theorem restrictArrays_reconstruct (rows repeats : Nat → Nat) (p : Path branch n j) :
    ∀ (r : Path branch j (i + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (record : OriginalWholeCut.Record rows repeats (p.append r) slots),
      WholeArraySubtreeSplit.restrictArrays rows p slots
          (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record) =
        OriginalWholeCut.reconstructRecord rows repeats r (cutSlots p slots)
          (descendRecord rows repeats p r slots record) := by
  induction p with
  | refl n =>
      intro r slots record
      cases r <;> rfl
  | step child p ih =>
      intro r slots record
      let lower : OriginalWholeCut.Record rows repeats (p.append r)
          (childSlots slots child) :=
        (record.1.2.1, (fun call => record.2.1 (.inr call), record.2.2))
      have hselected :
          (fun node => OriginalWholeCut.reconstructRecord rows repeats
            ((Path.step child p).append r) slots record (.inr (child, node))) =
            OriginalWholeCut.reconstructRecord rows repeats (p.append r)
              (childSlots slots child) lower := by
        funext node
        exact congrFun (WholeArraySampler.childrenAt_selected slots rows child
          (OriginalWholeCut.reconstructRecord rows repeats (p.append r)
            (childSlots slots child) lower) record.1.2.2) node
      exact (congrArg (WholeArraySubtreeSplit.restrictArrays rows p
        (childSlots slots child)) hselected).trans (ih r (childSlots slots child) lower)

theorem rootRows_reconstruct (rows repeats : Nat → Nat)
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats r slots) :
    OriginalWholeCut.reconstructRecord rows repeats r slots record (.inl ()) =
      BucketSampler.evaluate (rows (j + 1)) (id : H slots → H slots)
        (rootBuckets rows repeats r slots record) := by
  cases r <;> rfl

theorem selectedRows_reconstruct (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots) :
    SelectedArrayReplacement.selectedRows rows p slots
        (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record) =
      BucketSampler.evaluate (rows (j + 1)) (id : H (cutSlots p slots) → _)
        (upperBuckets rows repeats p r slots record) := by
  unfold SelectedArrayReplacement.selectedRows
  rw [restrictArrays_reconstruct]
  exact rootRows_reconstruct rows repeats r (cutSlots p slots) _

theorem descendRecord_readRecord (rows repeats : Nat → Nat) (p : Path branch n j) :
    ∀ (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots),
      descendRecord rows repeats p r slots
          (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) =
        OriginalWholeCut.readRecord rows repeats r chosen q (cutSlots p slots)
          (descendTape rows repeats p r chosen q slots tape) := by
  induction p with
  | refl n =>
      intro r chosen q slots tape
      cases r <;> rfl
  | step child p ih =>
      intro r chosen q slots tape
      exact ih r chosen q (childSlots slots child) (tape (.inr (.inl ())))

theorem rootBuckets_readRecord (rows repeats : Nat → Nat)
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch (j + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (r.append (.step chosen q)) slots) :
    rootBuckets rows repeats r slots (OriginalWholeCut.readRecord rows repeats r chosen q slots tape) =
      fun direction => RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain slots) (continuedRootTape rows repeats r chosen q slots tape direction) := by
  cases r with
  | refl => rfl
  | step child r =>
      funext direction
      exact OriginalScalarReconstruction.reconstruct_original F2 repeats (.step child r)
        (LeafDomain slots) (.step chosen q) (tape (.inl ()) direction)

theorem upperBuckets_readRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots) :
    upperBuckets rows repeats p r slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) =
      fun direction => RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots))
        (continuedRootTape rows repeats r chosen q (cutSlots p slots)
          (descendTape rows repeats p r chosen q slots tape) direction) := by
  unfold upperBuckets
  rw [descendRecord_readRecord, rootBuckets_readRecord]

theorem matrix_reconstruct (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots) :
    NodeEmbedding.matrix (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record)
        (upperNode p) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (CutNodeRows.bucketTapeEquiv rows p slots (upperBuckets rows repeats p r slots record)) := by
  rw [← CutNodeRows.matrixOfRows_selectedRows, selectedRows_reconstruct]
  exact CutNodeRows.matrixOfRows_evaluate rows p slots _

theorem matrix_replaceArrays (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    NodeEmbedding.matrix (replaceArrays rows repeats p r slots record a fresh) (upperNode p) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (Function.update
          (CutNodeRows.bucketTapeEquiv rows p slots (upperBuckets rows repeats p r slots record))
          (CutNodeRows.directionEquiv rows p a) (CutNodeRows.cutRowEquiv p slots fresh)) := by
  rw [← CutNodeRows.matrixOfRows_selectedRows]
  unfold replaceArrays
  rw [SelectedArrayReplacement.selectedRows_replace, CutNodeRows.matrixOfRows_evaluate,
    CutNodeRows.bucketTapeEquiv_update]

theorem pairRecord_eq (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats (p.append r) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    pairRecord rows repeats p r slots record a fresh =
      HierarchicalAgreementMean.pairRecord slots (upperNode p)
        (HierarchicalMatrixTable.backgroundOf slots (upperNode p)
          (OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots record),
          CutNodeRows.bucketSampleEquiv rows p slots
            (a, (upperBuckets rows repeats p r slots record, fresh))) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact matrix_reconstruct rows repeats p r slots record
    · exact matrix_replaceArrays rows repeats p r slots record a fresh

theorem enlargedPairRecord_read (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (j + 1)))
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    enlargedPairRecord rows repeats p r slots
        (a, UpperScalarCutReconstruction.read rows repeats p r chosen q slots tapes) =
      pairRecord rows repeats p r slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1) a
        (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)) tapes.2) := by
  change pairRecord rows repeats p r slots
    (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1) a
    (UpperScalarCutReconstruction.reconstructFresh repeats p r slots
      (UpperScalarCutReconstruction.readFresh repeats p r (.step chosen q) slots tapes.2)) = _
  rw [UpperScalarCutReconstruction.reconstructFresh_readFresh]

end
end PerfectCompleteness.UpperScalarCutBucket

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalCutPairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m k t : Nat}

attribute [local instance] OAI.PerfectCompleteness.OriginalCutPairLaw.backgroundFintype
attribute [local instance] OAI.PerfectCompleteness.OriginalCutPairLaw.rowSpaceFintype
theorem matrix_reconstruct (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats p slots) :
    NodeEmbedding.matrix (OriginalWholeCut.reconstructRecord rows repeats p slots record)
        (upperNode p) =
      BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (CutNodeRows.bucketTapeEquiv rows p slots
          (OriginalCutBucketReplacement.ownValues rows repeats p slots record.2.1)) := by
  rw [← CutNodeRows.matrixOfRows_selectedRows]
  change CutNodeRows.matrixOfRows rows p slots
    (SelectedArrayReplacement.selectedRows rows p slots
      (OriginalWholeCut.reconstruct rows repeats p slots record.1 record.2.1 record.2.2)) = _
  rw [OriginalCutBucketReplacement.selectedRows_reconstruct]
  exact CutNodeRows.matrixOfRows_evaluate rows p slots _

theorem pairRecord_eq (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (sample : BucketSampler.Direction (rows (m + 1)) ×
      OriginalExtraCutComparison.Record rows repeats p slots) :
    OriginalCutCollision.pairRecord rows repeats p slots sample =
      transportPair rows p slots (OriginalCutBucketLaw.read rows repeats p slots sample) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change NodeEmbedding.matrix
        (OriginalWholeCut.reconstructRecord rows repeats p slots
          (OriginalCutCollision.oldRecord rows repeats p slots sample.2)) (upperNode p) = _
      rw [matrix_reconstruct]
      rfl
    · change NodeEmbedding.matrix
        (OriginalWholeCut.reconstructRecord rows repeats p slots
          (OriginalCutBucketReplacement.replaceRecord rows repeats p slots
            (OriginalCutCollision.oldRecord rows repeats p slots sample.2) sample.1 sample.2.2))
          (upperNode p) = _
      rw [matrix_reconstruct]
      change BucketMatrixResampling.assembledMatrix (NodeEmbedding.RowSpace slots (upperNode p))
        (rows (Nodes.height (upperNode p)))
        (CutNodeRows.bucketTapeEquiv rows p slots
          (OriginalCutBucketReplacement.ownValues rows repeats p slots
            (OriginalCutBucketReplacement.replaceValues rows repeats p slots
              (OriginalCutCollision.oldRecord rows repeats p slots sample.2).2.1
                sample.1 sample.2.2))) = _
      rw [OriginalCutBucketReplacement.ownValues_replaceValues,
        CutNodeRows.bucketTapeEquiv_update]
      rfl

end
end PerfectCompleteness.OriginalCutPairLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutErasure
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutErasure

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

private theorem evaluate_cast (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {u v : Path branch n k} (h : u = v)
    (tape : WholeArraySampler.Tape rows repeats u slots) :
    WholeArraySampler.evaluate rows repeats v slots
        (Equiv.cast (congrArg (fun path => WholeArraySampler.Tape rows repeats path slots) h) tape) =
      WholeArraySampler.evaluate rows repeats u slots tape := by
  cases h
  rfl

theorem evaluate_assocTapeEquiv (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats ((p.append r).append q) slots) :
    WholeArraySampler.evaluate rows repeats (p.append (r.append q)) slots
        (assocTapeEquiv rows repeats p r q slots tape) =
      WholeArraySampler.evaluate rows repeats ((p.append r).append q) slots tape :=
  evaluate_cast rows repeats slots (p.append_assoc r q) tape

private theorem cast_step_selected (rows repeats : Nat → Nat) (child : Fin (branch n))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    {u v : Path branch n k} (h : u = v)
    (tape : WholeArraySampler.Tape rows repeats (.step child u) slots) :
    (Equiv.cast (congrArg (fun path => WholeArraySampler.Tape rows repeats path slots)
        (congrArg (Path.step child) h)) tape) (.inr (.inl ())) =
      Equiv.cast (congrArg
        (fun path => WholeArraySampler.Tape rows repeats path (childSlots slots child)) h)
        (tape (.inr (.inl ()))) := by
  cases h
  rfl

theorem assocTapeEquiv_selected (rows repeats : Nat → Nat) (child : Fin (branch n))
    (p : Path branch n j) (r : Path branch j i) (q : Path branch i k)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (((Path.step child p).append r).append q) slots) :
    (assocTapeEquiv rows repeats (.step child p) r q slots tape) (.inr (.inl ())) =
      assocTapeEquiv rows repeats p r q (childSlots slots child) (tape (.inr (.inl ()))) :=
  cast_step_selected rows repeats child slots (p.append_assoc r q) tape

theorem extract_assocTapeEquiv (rows repeats : Nat → Nat) (p : Path branch n j) :
    ∀ (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots),
      WholeArraySubtreeSplit.extract rows repeats p (r.append (.step chosen q)) slots
          (assocTapeEquiv rows repeats p r (.step chosen q) slots tape) =
        UpperScalarCutBucket.descendTape rows repeats p r chosen q slots tape := by
  induction p with
  | refl n => intro r chosen q slots tape; rfl
  | step child p ih =>
      intro r chosen q slots tape
      rw [WholeArraySubtreeSplit.extract_step, assocTapeEquiv_selected]
      exact ih r chosen q (childSlots slots child) (tape (.inr (.inl ())))

theorem upperReadRecord_reconstruct (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots) :
    OriginalWholeCut.reconstructRecord rows repeats p slots
        (upperReadRecord rows repeats p r chosen q slots tape) =
      WholeArraySampler.evaluate rows repeats (p.append (r.append (.step chosen q))) slots tape := by
  cases r with
  | refl => exact OriginalWholeCut.reconstruct_original rows repeats p chosen q slots tape
  | step upperChild tail =>
      exact OriginalWholeCut.reconstruct_original rows repeats p upperChild
        (tail.append (.step chosen q)) slots tape

theorem ownValues_readRecord (rows repeats : Nat → Nat) (p : Path branch n (j + 1)) :
    ∀ (chosen : Fin (branch j)) (q : Path branch j k)
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) slots),
      OriginalCutBucketReplacement.ownValues rows repeats p slots
          (OriginalWholeCut.readRecord rows repeats p chosen q slots tape).2.1 =
        fun direction => RecursiveSampler.evaluate F2 repeats (.step chosen q)
          (LeafDomain (cutSlots p slots))
          ((WholeArraySubtreeSplit.extract rows repeats p (.step chosen q) slots tape)
            (.inl ()) direction) := by
  induction n generalizing j with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro chosen q slots tape; rfl
      | step child p =>
          intro chosen q slots tape
          exact ih p chosen q (childSlots slots child) (tape (.inr (.inl ())))

theorem upperReadRecord_ownValues (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots) :
    OriginalCutBucketReplacement.ownValues rows repeats p slots
        (upperReadRecord rows repeats p r chosen q slots tape).2.1 =
      fun direction => RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots))
        (UpperScalarCutBucket.continuedRootTape rows repeats r chosen q (cutSlots p slots)
          (WholeArraySubtreeSplit.extract rows repeats p (r.append (.step chosen q)) slots tape)
          direction) := by
  cases r with
  | refl => exact ownValues_readRecord rows repeats p chosen q slots tape
  | step upperChild tail =>
      exact ownValues_readRecord rows repeats p upperChild (tail.append (.step chosen q)) slots tape

private theorem originalPairRecord_numberRecord (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : OriginalWholeCut.Record rows repeats p slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    OriginalCutCollision.pairRecord rows repeats p slots
        (a, (OriginalWholeCutBridge.numberRecord rows repeats p slots record, fresh)) =
      HierarchicalAgreementMean.pairRecord slots (upperNode p)
        (HierarchicalMatrixTable.backgroundOf slots (upperNode p)
          (OriginalWholeCut.reconstructRecord rows repeats p slots record),
          CutNodeRows.bucketSampleEquiv rows p slots
            (a, (OriginalCutBucketReplacement.ownValues rows repeats p slots record.2.1, fresh))) := by
  simpa only [OriginalCutPairLaw.transportPair, OriginalCutBucketLaw.read,
    OriginalCutCollision.oldArrays, OriginalCutBucketLaw.oldRecord_numberRecord] using
      OriginalCutPairLaw.pairRecord_eq rows repeats p slots
        (a, (OriginalWholeCutBridge.numberRecord rows repeats p slots record, fresh))

theorem upperBuckets_eq_ownValues (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots) :
    UpperScalarCutBucket.upperBuckets rows repeats p r slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) =
      OriginalCutBucketReplacement.ownValues rows repeats p slots
        (upperReadRecord rows repeats p r chosen q slots
          (assocTapeEquiv rows repeats p r (.step chosen q) slots tape)).2.1 := by
  rw [UpperScalarCutBucket.upperBuckets_readRecord, upperReadRecord_ownValues,
    extract_assocTapeEquiv]

theorem pairRecord_read_eq_upper (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (tape : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p slots)) :
    UpperScalarCutBucket.pairRecord rows repeats p r slots
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) a fresh =
      upperPairRecord rows repeats p r chosen q slots
        (assocTapeEquiv rows repeats p r (.step chosen q) slots tape) a fresh := by
  have harrays :
      OriginalWholeCut.reconstructRecord rows repeats (p.append r) slots
          (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tape) =
        OriginalWholeCut.reconstructRecord rows repeats p slots
          (upperReadRecord rows repeats p r chosen q slots
            (assocTapeEquiv rows repeats p r (.step chosen q) slots tape)) := by
    rw [OriginalWholeCut.reconstruct_original, upperReadRecord_reconstruct,
      evaluate_assocTapeEquiv]
  rw [UpperScalarCutBucket.pairRecord_eq]
  unfold upperPairRecord
  rw [originalPairRecord_numberRecord, harrays, upperBuckets_eq_ownValues]

theorem enlargedPairRecord_read_eq_upper (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (j + 1)))
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    UpperScalarCutBucket.enlargedPairRecord rows repeats p r slots
        (a, UpperScalarCutReconstruction.read rows repeats p r chosen q slots tapes) =
      upperPairRecord rows repeats p r chosen q slots
        (assocTapeEquiv rows repeats p r (.step chosen q) slots tapes.1) a
        (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)) tapes.2) := by
  rw [UpperScalarCutBucket.enlargedPairRecord_read]
  exact pairRecord_read_eq_upper rows repeats p r chosen q slots tapes.1 a _

theorem numberedPairRecord_read_eq_upper (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (a : BucketSampler.Direction (rows (j + 1)))
    (tapes : WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
      RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) :
    UpperScalarCutBucket.numberedPairRecord rows repeats p r slots
        (a, UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots
          (UpperScalarCutReconstruction.read rows repeats p r chosen q slots tapes)) =
      upperPairRecord rows repeats p r chosen q slots
        (assocTapeEquiv rows repeats p r (.step chosen q) slots tapes.1) a
        (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)) tapes.2) := by
  rw [UpperScalarCutBucket.numberedPairRecord_numberRecord]
  exact enlargedPairRecord_read_eq_upper rows repeats p r chosen q slots a tapes

end
end PerfectCompleteness.UpperScalarCutErasure

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape UpperScalarCutReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i k t : Nat}

private theorem scalarLaw_cast (repeats : Nat → Nat) (suffix : Path branch i k)
    (slots slots' : Slots branch i → Fin t → MixedSupport.Slot) (h : slots = slots') :
    (RecursiveSampler.law F2 repeats suffix (LeafDomain slots')).pushforward
        (Equiv.cast (congrArg
          (fun s : Slots branch i → Fin t → MixedSupport.Slot => ↥(H s)) h)).symm =
      RecursiveSampler.law F2 repeats suffix (LeafDomain slots) := by
  cases h
  change (RecursiveSampler.law F2 repeats suffix (LeafDomain slots)).pushforward id = _
  exact FiniteDistribution.pushforward_id _

theorem cutSpaceEquiv_scalarLaw (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (RecursiveSampler.law F2 repeats suffix
        (r.family (LeafDomain (cutSlots p slots)))).pushforward
          (cutSpaceEquiv p r slots).symm =
      RecursiveSampler.law F2 repeats suffix (LeafDomain (cutSlots (p.append r) slots)) :=
  scalarLaw_cast repeats suffix (cutSlots (p.append r) slots)
    (cutSlots r (cutSlots p slots)) (cutSlots_append p r slots)

theorem readFresh_law (repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (suffix : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (RecursiveSampler.tapeLaw F2 repeats (r.append suffix) (LeafDomain (cutSlots p slots))).pushforward
      (readFresh repeats p r suffix slots) =
        (freshValuesLaw repeats p r suffix slots).product (freshExteriorLaw repeats p r slots) := by
  let A := LeafDomain (cutSlots p slots)
  let scalarTape := RecursiveSampler.tapeLaw F2 repeats suffix (r.family A)
  let value : RecursiveSampler.Tape F2 repeats suffix (r.family A) →
      H (cutSlots (p.append r) slots) := fun tape =>
    (cutSpaceEquiv p r slots).symm (RecursiveSampler.evaluate F2 repeats suffix (r.family A) tape)
  let callsValue : OriginalTerminalSplit.TerminalTape F2 repeats r suffix A →
      FreshValues repeats p r slots := fun tapes call => value (tapes call)
  have hvalue : scalarTape.pushforward value =
      RecursiveSampler.law F2 repeats suffix (LeafDomain (cutSlots (p.append r) slots)) := by
    calc
      _ = (RecursiveSampler.law F2 repeats suffix (r.family A)).pushforward
          (cutSpaceEquiv p r slots).symm :=
        (FiniteDistribution.pushforward_comp scalarTape
          (RecursiveSampler.evaluate F2 repeats suffix (r.family A))
          (cutSpaceEquiv p r slots).symm).symm
      _ = _ := cutSpaceEquiv_scalarLaw repeats p r suffix slots
  have hcalls : (OriginalTerminalSplit.terminalLaw F2 repeats r suffix A).pushforward
      callsValue = freshValuesLaw repeats p r suffix slots := by
    calc
      _ = FiniteProduct.law (fun _ : TerminalCalls.TerminalIndex repeats r =>
          scalarTape.pushforward value) :=
        FiniteProduct.pushforward_map
          (fun _ : TerminalCalls.TerminalIndex repeats r => scalarTape) (fun _ => value)
      _ = _ := congrArg (fun μ : FiniteDistribution (H (cutSlots (p.append r) slots)) =>
        FiniteProduct.law (fun _ : TerminalCalls.TerminalIndex repeats r => μ)) hvalue
  calc
    _ = ((RecursiveSampler.tapeLaw F2 repeats (r.append suffix) A).pushforward
        (OriginalTerminalSplit.splitTape F2 repeats r suffix A)).pushforward
          (fun z => (callsValue z.1, z.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((OriginalTerminalSplit.terminalLaw F2 repeats r suffix A).product
        (OriginalTerminalSplit.exteriorLaw F2 repeats r A)).pushforward
          (fun z => (callsValue z.1, z.2)) := by
      rw [OriginalTerminalSplit.split_tapeLaw]
    _ = ((OriginalTerminalSplit.terminalLaw F2 repeats r suffix A).pushforward
        callsValue).product
          ((OriginalTerminalSplit.exteriorLaw F2 repeats r A).pushforward id) :=
      FiniteDistribution.product_pushforward
        (OriginalTerminalSplit.terminalLaw F2 repeats r suffix A)
        (OriginalTerminalSplit.exteriorLaw F2 repeats r A) callsValue id
    _ = _ := by simp only [hcalls, FiniteDistribution.pushforward_id, freshExteriorLaw, A]

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

theorem pack_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((OriginalWholeCutLaw.recordLaw rows repeats (p.append r) chosen q slots).product
      ((freshValuesLaw repeats p r (.step chosen q) slots).product
        (freshExteriorLaw repeats p r slots))).pushforward (packEquiv rows repeats p r slots) =
      recordLaw rows repeats p r chosen q slots := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  let scalar := RecursiveSampler.law F2 repeats (.step chosen q)
    (LeafDomain (cutSlots (p.append r) slots))
  change
    (OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).weight z.1.1 *
        ((∏ call : OriginalCutCalls.Index rows repeats (p.append r),
            scalar.weight (z.2.1 (.inl call))) *
          (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
            (cutSlots (p.append r) slots)).weight z.2.2) *
      ((∏ call : TerminalCalls.TerminalIndex repeats r,
          scalar.weight (z.2.1 (.inr call))) *
        (freshExteriorLaw repeats p r slots).weight z.1.2) =
      ((OriginalWholeCutTape.exteriorLaw rows repeats (p.append r) slots).weight z.1.1 *
        (freshExteriorLaw repeats p r slots).weight z.1.2) *
          ((∏ call : OriginalCutCalls.Index rows repeats (p.append r) ⊕
              TerminalCalls.TerminalIndex repeats r, scalar.weight (z.2.1 call)) *
            (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
              (cutSlots (p.append r) slots)).weight z.2.2)
  rw [Fintype.prod_sum_type]
  ring

theorem read_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots).product
      (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots)))).pushforward
          (read rows repeats p r chosen q slots) =
      recordLaw rows repeats p r chosen q slots := by
  calc
    _ = (((WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots).product
        (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)))).pushforward
            (fun tapes =>
              (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots tapes.1,
                readFresh repeats p r (.step chosen q) slots tapes.2))).pushforward
                  (packEquiv rows repeats p r slots) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (((WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots).pushforward
        (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots)).product
          ((RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
            (LeafDomain (cutSlots p slots))).pushforward
              (readFresh repeats p r (.step chosen q) slots))).pushforward
                (packEquiv rows repeats p r slots) := by
      exact congrArg
        (fun μ : FiniteDistribution (OriginalWholeCut.Record rows repeats (p.append r) slots ×
            FreshRecord repeats p r slots) => μ.pushforward (packEquiv rows repeats p r slots))
        (FiniteDistribution.product_pushforward
          (WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots)
          (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
            (LeafDomain (cutSlots p slots)))
          (OriginalWholeCut.readRecord rows repeats (p.append r) chosen q slots)
          (readFresh repeats p r (.step chosen q) slots))
    _ = _ := by
      rw [OriginalWholeCutLaw.readRecord_law, readFresh_law]
      exact pack_law rows repeats p r chosen q slots

theorem numberRecord_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (recordLaw rows repeats p r chosen q slots).pushforward (numberRecordEquiv rows repeats p r slots) =
      (exteriorLaw rows repeats p r slots).product
        ((OriginalChildBlocks.sourceLaw (UpperScalarCutCalls.count rows repeats n j (i + 1))
          rows repeats chosen q (cutSlots (p.append r) slots)).pushforward
            (OriginalChildBlocks.observed (UpperScalarCutCalls.count rows repeats n j (i + 1))
              rows repeats chosen q (cutSlots (p.append r) slots))) := by
  rw [OriginalWholeCutBridge.observed_product_law,
    ← FiniteDistribution.transport_eq_pushforward
      (recordLaw rows repeats p r chosen q slots) (numberRecordEquiv rows repeats p r slots)]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  let scalar := RecursiveSampler.law F2 repeats (.step chosen q)
    (LeafDomain (cutSlots (p.append r) slots))
  change (exteriorLaw rows repeats p r slots).weight z.1 *
      ((∏ call : UpperScalarCutCalls.Index rows repeats p r,
          scalar.weight (z.2.1 (UpperScalarCutCalls.numbering rows repeats p r call))) *
        (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
          (cutSlots (p.append r) slots)).weight z.2.2) =
    (exteriorLaw rows repeats p r slots).weight z.1 *
      ((∏ call : Fin (UpperScalarCutCalls.count rows repeats n j (i + 1)),
          scalar.weight (z.2.1 call)) *
        (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
          (cutSlots (p.append r) slots)).weight z.2.2)
  exact congrArg (fun w : ℝ => (exteriorLaw rows repeats p r slots).weight z.1 *
      (w * (OriginalWholeCutLaw.belowArraysLaw rows repeats chosen q
        (cutSlots (p.append r) slots)).weight z.2.2))
    ((UpperScalarCutCalls.numbering rows repeats p r).prod_comp
      (fun call => scalar.weight (z.2.1 call)))

theorem numbered_read_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j (i + 1)) (chosen : Fin (branch i)) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots).product
      (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots)))).pushforward
          (fun tapes => numberRecordEquiv rows repeats p r slots
            (read rows repeats p r chosen q slots tapes)) =
      (exteriorLaw rows repeats p r slots).product
        ((OriginalChildBlocks.sourceLaw (UpperScalarCutCalls.count rows repeats n j (i + 1))
          rows repeats chosen q (cutSlots (p.append r) slots)).pushforward
            (OriginalChildBlocks.observed (UpperScalarCutCalls.count rows repeats n j (i + 1))
              rows repeats chosen q (cutSlots (p.append r) slots))) := by
  rw [← FiniteDistribution.pushforward_comp, read_law, numberRecord_law]

end
end PerfectCompleteness.UpperScalarCutLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarPairAveraging
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarPairAveraging

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

attribute [local instance] linearMapFintype

private theorem map_right {D A B Γ : Type*}
    [Fintype D] [Fintype A] [Fintype B] [Fintype Γ]
    (δ : FiniteDistribution D) (μ : FiniteDistribution A)
    (f : A → B) (g : D × B → Γ) :
    (δ.product (μ.pushforward f)).pushforward g =
      (δ.product μ).pushforward (fun z => g (z.1, f z.2)) := by
  have h := FiniteDistribution.product_pushforward δ μ id f
  simp only [FiniteDistribution.pushforward_id, id_eq] at h
  rw [← h, FiniteDistribution.pushforward_comp]

private theorem map_three {D A B A' B' Γ : Type*}
    [Fintype D] [Fintype A] [Fintype B] [Fintype A'] [Fintype B'] [Fintype Γ]
    (δ : FiniteDistribution D) (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (f : A → A') (g : B → B') (observe : D × (A' × B') → Γ) :
    (δ.product ((μ.pushforward f).product (ν.pushforward g))).pushforward observe =
      (δ.product (μ.product ν)).pushforward
        (fun z => observe (z.1, (f z.2.1, g z.2.2))) := by
  rw [← FiniteDistribution.product_pushforward μ ν f g]
  exact map_right δ (μ.product ν) (fun z => (f z.1, g z.2)) observe

variable {branch : Nat → Nat} {n j i k t : Nat}

attribute [local instance] OAI.PerfectCompleteness.UpperScalarPairAveraging.backgroundFintype
local instance rowSpaceFintype_r32eec7_1 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
private theorem tapeLaw_cast (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {u v : Path branch n k} (h : u = v) :
    (WholeArraySampler.tapeLaw rows repeats u slots).pushforward
        (Equiv.cast (congrArg (fun path => WholeArraySampler.Tape rows repeats path slots) h)) =
      WholeArraySampler.tapeLaw rows repeats v slots := by
  cases h
  change (WholeArraySampler.tapeLaw rows repeats u slots).pushforward id = _
  exact FiniteDistribution.pushforward_id _

theorem assocTapeEquiv_law (rows repeats : Nat → Nat) (p : Path branch n j)
    (r : Path branch j i) (q : Path branch i k)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (WholeArraySampler.tapeLaw rows repeats ((p.append r).append q) slots).pushforward
        (UpperScalarCutErasure.assocTapeEquiv rows repeats p r q slots) =
      WholeArraySampler.tapeLaw rows repeats (p.append (r.append q)) slots :=
  tapeLaw_cast rows repeats slots (p.append_assoc r q)

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

private theorem upper_step_tape_law (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (chosen : Fin (branch j)) (q : Path branch j 0)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (directions.product
      ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots).product
        (RecursiveSampler.tapeLaw F2 repeats (.step chosen q)
          (LeafDomain (cutSlots p slots))))).pushforward
      (fun z => OriginalCutCollision.pairRecord rows repeats p slots
        (z.1, (OriginalWholeCutBridge.numberRecord rows repeats p slots
          (OriginalWholeCut.readRecord rows repeats p chosen q slots z.2.1),
          RecursiveSampler.evaluate F2 repeats (.step chosen q)
            (LeafDomain (cutSlots p slots)) z.2.2))) =
      pathPairLaw rows repeats p slots directions (.step chosen q) := by
  let : Fintype (OriginalWholeCut.Values rows repeats p slots ×
      OriginalWholeCut.BelowArrays rows p slots) :=
    OriginalWholeCutLaw.valuesBelowFintype rows repeats p slots
  rw [← map_three directions
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots)
    (RecursiveSampler.tapeLaw F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))
    (fun tape => OriginalWholeCutBridge.numberRecord rows repeats p slots
      (OriginalWholeCut.readRecord rows repeats p chosen q slots tape))
    (RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain (cutSlots p slots)))
    (OriginalCutCollision.pairRecord rows repeats p slots)]
  rw [← FiniteDistribution.pushforward_comp
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) slots)
    (OriginalWholeCut.readRecord rows repeats p chosen q slots)
    (OriginalWholeCutBridge.numberRecord rows repeats p slots),
    OriginalWholeCutLaw.readRecord_law]
  rfl

private theorem upper_read_law (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (chosen : Fin (branch i)) (q : Path branch i 0)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (directions.product
      ((WholeArraySampler.tapeLaw rows repeats (p.append (r.append (.step chosen q))) slots).product
        (RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots))))).pushforward
      (fun z => UpperScalarCutErasure.upperPairRecord rows repeats p r chosen q slots z.2.1 z.1
        (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
          (LeafDomain (cutSlots p slots)) z.2.2)) =
      pathPairLaw rows repeats p slots directions (r.append (.step chosen q)) := by
  cases r with
  | refl => exact upper_step_tape_law rows repeats p chosen q slots directions
  | step upperChild tail =>
      exact upper_step_tape_law rows repeats p upperChild (tail.append (.step chosen q)) slots directions

theorem fixed_pairLaw_oai (rows repeats : Nat → Nat)
    (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
    (chosen : Fin (branch i)) (q : Path branch i 0)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      ((OriginalChildBlocks.sourceLaw (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1))
        rows repeats chosen q (cutSlots (p.append r) slots)).pushforward
          (OriginalChildBlocks.observed (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1))
            rows repeats chosen q (cutSlots (p.append r) slots))) =
      pathPairLaw rows repeats p slots directions (r.append (.step chosen q)) := by
  let oldTape := WholeArraySampler.tapeLaw rows repeats ((p.append r).append (.step chosen q)) slots
  let freshTape := RecursiveSampler.tapeLaw F2 repeats (r.append (.step chosen q))
    (LeafDomain (cutSlots p slots))
  let observe := fun z : BucketSampler.Direction (rows (j + 1)) ×
      (WholeArraySampler.Tape rows repeats (p.append (r.append (.step chosen q))) slots ×
        RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) =>
    UpperScalarCutErasure.upperPairRecord rows repeats p r chosen q slots z.2.1 z.1
      (RecursiveSampler.evaluate F2 repeats (r.append (.step chosen q))
        (LeafDomain (cutSlots p slots)) z.2.2)
  unfold UpperScalarPairComparison.pairLaw
  rw [← UpperScalarCutLaw.numbered_read_law rows repeats p r chosen q slots, map_right]
  have hmap :
      (fun z : BucketSampler.Direction (rows (j + 1)) ×
        (WholeArraySampler.Tape rows repeats ((p.append r).append (.step chosen q)) slots ×
          RecursiveSampler.Tape F2 repeats (r.append (.step chosen q)) (LeafDomain (cutSlots p slots))) =>
        UpperScalarCutBucket.numberedPairRecord rows repeats p r slots
          (z.1, UpperScalarCutReconstruction.numberRecordEquiv rows repeats p r slots
            (UpperScalarCutReconstruction.read rows repeats p r chosen q slots z.2))) =
        (fun z => observe (z.1,
          (UpperScalarCutErasure.assocTapeEquiv rows repeats p r (.step chosen q) slots z.2.1,
            id z.2.2))) := by
    funext z
    exact UpperScalarCutErasure.numberedPairRecord_read_eq_upper
      rows repeats p r chosen q slots z.1 z.2
  rw [hmap, ← map_three directions oldTape freshTape
    (UpperScalarCutErasure.assocTapeEquiv rows repeats p r (.step chosen q) slots) id observe]
  dsimp only [oldTape]
  rw [assocTapeEquiv_law, FiniteDistribution.pushforward_id]
  exact upper_read_law rows repeats p r chosen q slots directions

end
end PerfectCompleteness.UpperScalarPairAveraging

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.UpperScalarPairAveraging.fixed_pairLaw_oai := @OAI.PerfectCompleteness.UpperScalarPairAveraging.fixed_pairLaw_oai
