-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedHighBound.directionMean_square_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:23:22.401197+00:00
-- url     : https://prove2.me/submissions/96dcc676-7de5-4768-9b59-191368cf302b

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
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.TensorProduct.Associator
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
import Definitions.Def_OAIQ252P018
import Theorems.Thm_OAI_PerfectCompleteness_CleanPhysicalHighAverage_physical_probability_eq_observed
import Theorems.Thm_OAI_PerfectCompleteness_CleanPhysicalHighEvent_mean_probability_eq
import Theorems.Thm_OAI_PerfectCompleteness_FixedSourceGlobalCollision_mean_local_le
import Theorems.Thm_OAI_PerfectCompleteness_FixedSourcePhysicalHigh_probability_square_le_collision
import Theorems.Thm_OAI_PerfectCompleteness_SourceQuestionPhysicalCollision_rawEvent_observe

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact finite sampling laws used to identify verifier distributions with repeated
game question laws. These are finite sum/product identities, not independence
assumptions about an unspecified distribution.
-/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section

theorem iid_uniform {Ω : Type*} [Fintype Ω] [Nonempty Ω] (n : Nat) :
    (uniform Ω).iid n = uniform (Fin n → Ω) := by
  classical
  apply eq_of_weight_eq
  intro x
  simp [iid, uniform, Nat.cast_pow, one_div]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

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

theorem pushforward_mixture (μ : FiniteDistribution A) (ν : A → FiniteDistribution B)
    (f : B → C) :
    (μ.mixture ν).pushforward f = μ.mixture (fun a => (ν a).pushforward f) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward, probability_mixture]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DependentPredictionDifferenceLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SigmaObservation

open UniqueGamesTheorem.Foundations.Games CompletionSoundness

noncomputable section

theorem eq_of_probability_eq {X : Type*} [Fintype X]
    (μ ν : FiniteDistribution X)
    (h : ∀ event : X → Bool, μ.probability event = ν.probability event) : μ = ν := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simpa [FiniteDistribution.probability] using h (fun y => decide (y = x))

end
end PerfectCompleteness.SigmaObservation

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceChildKernelLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernel

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays
open SourceQuestionReconstruction

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem projectedEquiv_law (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (FiniteProduct.law (fun j => FiniteDistribution.uniform
      (Factors (C := C) (t := t) rows clauses designated i s j))).pushforward
        (projectedEquiv (C := C) (t := t) rows clauses designated i s) =
      FiniteDistribution.uniform (Projected (C := C) (t := t) rows clauses designated i s) := by
  rw [UniformLinearImage.law_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card ((j : CleanTreeFactors.Index branch n (Fintype.card C) rows) →
    Factors (C := C) (t := t) rows clauses designated i s j) : ℝ) =
      1 / (Fintype.card (Projected (C := C) (t := t) rows clauses designated i s) : ℝ)
  rw [Fintype.card_congr (projectedEquiv (C := C) (t := t) rows clauses designated i s)]

theorem decodeNative_law (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (nonprojected (C := C) (t := t) rows clauses designated i s).pushforward
      (decodeNative rows clauses designated i s) =
        FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s) := by
  unfold nonprojected NativeTaggedUniform.kernel
  rw [FiniteDistribution.pushforward_comp]
  simp only [decodeNative_tagged]
  change (FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s)).pushforward
    (Equiv.refl _) = _
  rw [FiniteDistribution.pushforward_equiv]
  rfl

theorem decodeProjected_law (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (UniformLatent.latentKernel (Factors (C := C) (t := t) rows clauses designated i) s).pushforward
      (decodeProjected rows clauses designated i s) =
        FiniteDistribution.uniform (Projected (C := C) (t := t) rows clauses designated i s) := by
  rw [UniformLatent.latentKernel, FiniteDistribution.pushforward_comp]
  simp only [decodeProjected_tagged]
  exact projectedEquiv_law rows clauses designated i s

end
end PerfectCompleteness.SourceChildKernel

end

section

namespace PerfectCompleteness.SourceChildKernelJoint

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces SourceQuestionReconstruction

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem childrenLaw_group
    (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) →
      FiniteDistribution (SourceChildKernel.Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.childrenLaw (C := C) (t := t) rows clauses designated μ ν flag).pushforward
        (groupEquiv rows clauses designated) =
      CleanConditioning.kernelJoint
        (FiniteProduct.law (fun i => (μ i).product (ν i)))
        (fun sources => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i (sources i))) := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨sources, raw⟩
  change (∏ i : Fin (branch n),
      (μ i).weight (sources i).1 * ((ν i).weight (sources i).2 *
        (SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i
          (sources i)).weight (raw i))) =
    (∏ i : Fin (branch n), (μ i).weight (sources i).1 * (ν i).weight (sources i).2) *
      ∏ i : Fin (branch n),
        (SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i
          (sources i)).weight (raw i)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (mul_assoc _ _ _).symm

theorem originalLaw_group [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (groupEquiv rows clauses designated) =
      CleanConditioning.kernelJoint
        (FiniteProduct.law (fun i : Fin (branch n) =>
          (SourceOddLists.tupleLaw m t).product
            (FiniteProduct.law (fun _ : {leaf : Slots branch n // leaf ≠ designated i} =>
              SourceOddLists.tupleLaw m t))))
        (fun sources => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i (sources i))) :=
  childrenLaw_group rows clauses designated _ _ flag

end
end PerfectCompleteness.SourceChildKernelJoint

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildKernelLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernelLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem kernel_physical (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    (kernel (C := C) (t := t) rows clauses designated flag i s).pushforward
        (physical rows clauses designated i s) =
      physicalLaw (C := C) (t := t) rows clauses designated flag i s := by
  unfold kernel UniformLatent.projectedKernel physicalLaw
  rw [FiniteDistribution.pushforward_mixture]
  apply congrArg (fun laws : Bool →
    FiniteDistribution (Physical (C := C) (t := t) rows clauses designated i s) =>
      (flag i).mixture laws)
  funext b
  cases b with
  | false =>
      change ((nonprojected (C := C) (t := t) rows clauses designated i s).pushforward
        Sum.inl).pushforward (physical rows clauses designated i s) =
          (FiniteDistribution.uniform (Native (C := C) (t := t) rows clauses designated i s)).pushforward
            (fun block => (⟨false, block⟩ : Physical (C := C) (t := t) rows clauses designated i s))
      rw [FiniteDistribution.pushforward_comp]
      calc
        _ = ((nonprojected (C := C) (t := t) rows clauses designated i s).pushforward
            (decodeNative rows clauses designated i s)).pushforward
              (fun block => (⟨false, block⟩ :
                Physical (C := C) (t := t) rows clauses designated i s)) :=
          (FiniteDistribution.pushforward_comp _ _ _).symm
        _ = _ := by rw [decodeNative_law]
  | true =>
      change ((UniformLatent.latentKernel
        (Factors (C := C) (t := t) rows clauses designated i) s).pushforward
          Sum.inr).pushforward (physical rows clauses designated i s) =
            (FiniteDistribution.uniform
              (Projected (C := C) (t := t) rows clauses designated i s)).pushforward
                (fun block => (⟨true, block⟩ : Physical (C := C) (t := t) rows clauses designated i s))
      rw [FiniteDistribution.pushforward_comp]
      calc
        _ = ((UniformLatent.latentKernel
            (Factors (C := C) (t := t) rows clauses designated i) s).pushforward
              (decodeProjected rows clauses designated i s)).pushforward
                (fun block => (⟨true, block⟩ :
                  Physical (C := C) (t := t) rows clauses designated i s)) :=
          (FiniteDistribution.pushforward_comp _ _ _).symm
        _ = _ := by rw [decodeProjected_law]

theorem kernels_physical (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (fun raw i => physical rows clauses designated i (sources i) (raw i)) =
      FiniteProduct.law (fun i =>
        physicalLaw (C := C) (t := t) rows clauses designated flag i (sources i)) := by
  rw [FiniteProduct.pushforward_map]
  exact congrArg FiniteProduct.law
    (funext fun i => kernel_physical rows clauses designated flag i (sources i))

end
end PerfectCompleteness.SourceChildKernelLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourcePhysicalTaggedChildren
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalTaggedChildren

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces SourceChildKernel

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

private theorem physicalLaw_sigma (flag : Fin (branch n) → FiniteDistribution Bool)
    (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    SourceChildKernelLaw.physicalLaw (C := C) (t := t) rows clauses designated flag i s =
      CompletionSoundness.sigmaLaw (flag i) (fun b =>
        FiniteDistribution.uniform (Block C rows (mixedSlots clauses designated i s b))) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  unfold SourceChildKernelLaw.physicalLaw
  rw [FiniteDistribution.probability_mixture, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro b
  exact FiniteDistribution.probability_pushforward _ _ _

theorem pack_law (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      SourceChildKernelLaw.physicalLaw (C := C) (t := t) rows clauses designated flag i
        (sources i))).pushforward (pack rows clauses designated sources) =
      CompletionSoundness.sigmaLaw (FiniteProduct.law flag) (fun flags =>
        CutChildGrouping.rawLaw (C := C) (slots clauses designated sources flags) rows) := by
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  rintro ⟨flags, children⟩
  change (∏ i, (SourceChildKernelLaw.physicalLaw (C := C) (t := t)
      rows clauses designated flag i (sources i)).weight ⟨flags i, children i⟩) =
    (∏ i, (flag i).weight (flags i)) *
      (∏ i, (FiniteDistribution.uniform
        (Block C rows (mixedSlots clauses designated i (sources i) (flags i)))).weight
          (children i))
  simp_rw [physicalLaw_sigma]
  exact Finset.prod_mul_distrib

theorem kernels_tagged (flag : Fin (branch n) → FiniteDistribution Bool)
    (sources : Sources (m := m) (t := t) designated) :
    (FiniteProduct.law (fun i =>
      kernel (C := C) (t := t) rows clauses designated flag i (sources i))).pushforward
        (observe rows clauses designated sources) =
      CompletionSoundness.sigmaLaw (FiniteProduct.law flag) (fun flags =>
        CutChildGrouping.rawLaw (C := C) (slots clauses designated sources flags) rows) := by
  unfold observe
  rw [← FiniteDistribution.pushforward_comp, SourceChildKernelLaw.kernels_physical]
  exact pack_law rows clauses designated flag sources

end
end PerfectCompleteness.SourcePhysicalTaggedChildren

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerReplayTransportLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformConditioning

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] [Nonempty Ω] [Nonempty Γ]

theorem uniform_transport (e : Ω ≃ Γ) :
    (FiniteDistribution.uniform Ω).transport e = FiniteDistribution.uniform Γ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change 1 / (Fintype.card Ω : ℝ) = 1 / (Fintype.card Γ : ℝ)
  rw [Fintype.card_congr e]

end
end PerfectCompleteness.UniformConditioning

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildQuestionLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildQuestionLaw

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays SourceQuestionReconstruction
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t v : Nat}

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

theorem sourceLaw_uniform [NeZero m] (designated : Fin (branch n) → Slots branch n) :
    sourceLaw m t designated =
      FiniteDistribution.uniform (SourceChildKernel.Sources (m := m) (t := t) designated) := by
  simp only [sourceLaw, SourceOddLists.tupleLaw, FiniteDistribution.iid_uniform,
    UniformLinearImage.law_uniform, uniform_product]

end
end PerfectCompleteness.SourceChildQuestionLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionPositionSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPositionSplit

noncomputable section

open scoped Classical
open RecursiveSpaces SourceQuestionReconstruction TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m : Nat}

theorem sourceLaw_split [NeZero m] (designated : Fin (branch n) → Slots branch n) :
    (SourceChildQuestionLaw.sourceLaw m t designated).pushforward (split designated) =
      (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m)).product
        (FiniteDistribution.uniform (Positions (branch := branch) (n := n) (t := t))) := by
  rw [SourceChildQuestionLaw.sourceLaw_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (SourceChildKernel.Sources (m := m) (t := t) designated) : ℝ) =
    (1 / (Fintype.card (Questions (branch := branch) (n := n) (t := t) (m := m)) : ℝ)) *
      (1 / (Fintype.card (Positions (branch := branch) (n := n) (t := t)) : ℝ))
  rw [Fintype.card_congr (split (m := m) (t := t) designated), Fintype.card_prod,
    Nat.cast_mul, one_div_mul_one_div]

theorem positions_byChild :
    (FiniteDistribution.uniform (Positions (branch := branch) (n := n) (t := t))).pushforward
      (byChild (branch := branch) (n := n) (t := t)) =
      FiniteProduct.law (fun _ : Fin (branch n) =>
        FiniteDistribution.uniform (ChildPositions (branch := branch) (n := n) (t := t))) := by
  rw [UniformLinearImage.law_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card (Positions (branch := branch) (n := n) (t := t)) : ℝ) =
    1 / (Fintype.card (Fin (branch n) → ChildPositions (branch := branch) (n := n) (t := t)) : ℝ)
  rw [Fintype.card_congr (byChild (branch := branch) (n := n) (t := t))]

end
end PerfectCompleteness.SourceQuestionPositionSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionKernelJoint
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionKernelJoint

open scoped Classical
open RecursiveSpaces SourceQuestionPositionSplit
open UniqueGamesTheorem.Foundations.Games

noncomputable section

private theorem kernelJoint_pushforward_first {S T R : Type*}
    [Fintype S] [Fintype T] [Fintype R]
    (μ : FiniteDistribution S) (kernel : S → FiniteDistribution R) (e : S ≃ T) :
    (CleanConditioning.kernelJoint μ kernel).pushforward
        (Equiv.prodCongr e (Equiv.refl R)) =
      CleanConditioning.kernelJoint (μ.pushforward e) (fun s => kernel (e.symm s)) := by
  simp only [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro point
  rfl

variable {branch : Nat → Nat} {n t v m : Nat}

theorem sourceLaw_sourceEquiv [NeZero m]
    (designated : Fin (branch n) → Slots branch n) :
    (SourceChildQuestionLaw.sourceLaw m t designated).pushforward (sourceEquiv designated) =
      (PreliminarySampler.questionsLaw (branch := branch) (n := n + 1) (t := t) (m := m)).product
        (FiniteProduct.law (fun _ : Fin (branch n) =>
          FiniteDistribution.uniform (ChildPositions (branch := branch) (n := n) (t := t)))) := by
  calc
    _ = ((SourceChildQuestionLaw.sourceLaw m t designated).pushforward
        (SourceQuestionPositionSplit.split designated)).pushforward
          (Equiv.prodCongr (Equiv.refl _) SourceQuestionPositionSplit.byChild) := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = _ := by
      rw [SourceQuestionPositionSplit.sourceLaw_split]
      change ((PreliminarySampler.questionsLaw
          (branch := branch) (n := n + 1) (t := t) (m := m)).product
          (FiniteDistribution.uniform (Positions (branch := branch) (n := n) (t := t)))).pushforward
        (fun x => (id x.1, SourceQuestionPositionSplit.byChild x.2)) = _
      rw [FiniteDistribution.product_pushforward, FiniteDistribution.pushforward_id,
        SourceQuestionPositionSplit.positions_byChild]

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem originalLaw_group [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (groupEquiv rows clauses designated) =
      CleanConditioning.kernelJoint
        ((PreliminarySampler.questionsLaw
          (branch := branch) (n := n + 1) (t := t) (m := m)).product
            (FiniteProduct.law (fun _ : Fin (branch n) =>
              FiniteDistribution.uniform
                (ChildPositions (branch := branch) (n := n) (t := t)))))
        (fun qp => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i
            (sources designated qp.1 qp.2 i))) := by
  calc
    _ = ((SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).pushforward
        (SourceChildKernelJoint.groupEquiv rows clauses designated)).pushforward
          (Equiv.prodCongr (sourceEquiv designated) (Equiv.refl _)) := by
      rw [FiniteDistribution.pushforward_comp]
      rfl
    _ = (CleanConditioning.kernelJoint (SourceChildQuestionLaw.sourceLaw m t designated)
        (fun source => FiniteProduct.law (fun i =>
          SourceChildKernel.kernel (C := C) (t := t) rows clauses designated flag i
            (source i)))).pushforward
          (Equiv.prodCongr (sourceEquiv designated) (Equiv.refl _)) := by
      rw [SourceChildKernelJoint.originalLaw_group]
      rfl
    _ = _ := by
      rw [kernelJoint_pushforward_first, sourceLaw_sourceEquiv]
      rfl

end
end PerfectCompleteness.SourceQuestionKernelJoint

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionRawSwap
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionRawSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games

private theorem expectation_kernelJoint {S R : Type*} [Fintype S] [Fintype R]
    (μ : FiniteDistribution S) (P : S → FiniteDistribution R) (f : S × R → ℝ) :
    (CleanConditioning.kernelJoint μ P).expectation f =
      μ.expectation (fun s => (P s).expectation (fun r => f (s, r))) := by
  simp only [FiniteDistribution.expectation, CleanConditioning.kernelJoint,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

variable {branch : Nat → Nat} {root h n t v m : Nat}

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem originalLaw_expectation [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (F : PreliminarySampler.Questions branch (n + 1) t m →
      SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t) →
        SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated → ℝ) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).expectation
        (fun sample => F (insideQuestions rows clauses designated sample)
          (positions rows clauses designated sample) (raw rows clauses designated sample)) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := n + 1) (t := t) (m := m)).expectation
          (fun inside => (SourceProjectedTag.positionLaw
            (branch := branch) (n := n) (t := t)).expectation
              (fun choices => (kernelLaw rows clauses designated flag inside choices).expectation
                (F inside choices))) := by
  let statistic : (PreliminarySampler.Questions branch (n + 1) t m ×
      SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) ×
      SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated → ℝ :=
    fun grouped => F grouped.1.1 grouped.1.2 grouped.2
  have hgroup := congrArg (fun μ : FiniteDistribution
      ((PreliminarySampler.Questions branch (n + 1) t m ×
        SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) ×
        SourceChildKernelJoint.RawTuple (C := C) (t := t) rows clauses designated) =>
      μ.expectation statistic)
    (SourceQuestionKernelJoint.originalLaw_group (C := C) (t := t)
      rows clauses designated flag)
  simpa only [FiniteDistribution.expectation_pushforward, expectation_kernelJoint,
    FiniteDistribution.expectation_product, statistic, insideQuestions, positions, raw,
    kernelLaw, SourceProjectedTag.positionLaw] using hgroup

end
end PerfectCompleteness.SourceQuestionRawSwap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CandidateCoupling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CandidateCoupling

open PreliminarySampler PreliminaryAveraging TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

section Selection

variable {I : Type*} [Fintype I] [DecidableEq I]
  {D : I → Type*} [∀ i, Fintype (D i)]

omit [DecidableEq I] in
theorem expectation_sigmaLaw (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (D i)) (f : (Σ i, D i) → ℝ) :
    (CompletionSoundness.sigmaLaw μ ν).expectation f =
      μ.expectation (fun i => (ν i).expectation (fun d => f ⟨i, d⟩)) := by
  simp only [FiniteDistribution.expectation, CompletionSoundness.sigmaLaw,
    Fintype.sum_sigma, Finset.mul_sum, mul_assoc]

end Selection

end
end PerfectCompleteness.CandidateCoupling

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourcePhysicalChildExpectation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalChildExpectation

noncomputable section

open scoped Classical
open RecursiveSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem kernel_expectation
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (q : PreliminarySampler.Questions branch (n + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
    (F : (flags : SourceProjectedTag.Flags (branch := branch) (n := n)) →
      CutChildGrouping.Raw (C := C)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows → ℝ) :
    (SourceQuestionRawSwap.kernelLaw (C := C) rows clauses designated flag q choices).expectation
        (fun raw =>
          let observed := observe rows clauses designated q choices raw
          F observed.1 observed.2) =
      (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
        (CutChildGrouping.rawLaw (C := C)
          (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).expectation
            (F flags)) := by
  let statistic :
      (Σ flags : SourceProjectedTag.Flags (branch := branch) (n := n),
        CutChildGrouping.Raw (C := C)
          (SourceProjectedTag.mixedInside clauses designated q choices flags) rows) → ℝ :=
    fun observed => F observed.1 observed.2
  let physical := fun flags : SourceProjectedTag.Flags (branch := branch) (n := n) =>
    CutChildGrouping.rawLaw (C := C)
      (SourceProjectedTag.mixedInside clauses designated q choices flags) rows
  have hlaw :
      (SourceQuestionRawSwap.kernelLaw (C := C) rows clauses designated flag q choices).pushforward
          (observe rows clauses designated q choices) =
        CompletionSoundness.sigmaLaw (SourceProjectedTag.flagLaw flag) physical :=
    SourcePhysicalTaggedChildren.kernels_tagged (C := C) rows clauses designated flag
      (SourceQuestionKernelJoint.sources designated q choices)
  calc
    _ = ((SourceQuestionRawSwap.kernelLaw (C := C) rows clauses designated flag q choices).pushforward
        (observe rows clauses designated q choices)).expectation statistic :=
      (FiniteDistribution.expectation_pushforward
        (SourceQuestionRawSwap.kernelLaw (C := C) rows clauses designated flag q choices)
        (observe rows clauses designated q choices) statistic).symm
    _ = (CompletionSoundness.sigmaLaw (SourceProjectedTag.flagLaw flag) physical).expectation
        statistic := congrArg (fun μ => FiniteDistribution.expectation μ statistic) hlaw
    _ = _ := CandidateCoupling.expectation_sigmaLaw
      (SourceProjectedTag.flagLaw flag) physical statistic

theorem originalLaw_expectation [NeZero m]
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (F : (q : PreliminarySampler.Questions branch (n + 1) t m) →
      (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t)) →
      (flags : SourceProjectedTag.Flags (branch := branch) (n := n)) →
      CutChildGrouping.Raw (C := C)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows → ℝ) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated flag).expectation
        (fun sample =>
          let q := SourceQuestionRawSwap.insideQuestions rows clauses designated sample
          let choices := SourceQuestionRawSwap.positions rows clauses designated sample
          let observed := observe rows clauses designated q choices
            (SourceQuestionRawSwap.raw rows clauses designated sample)
          F q choices observed.1 observed.2) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := n + 1) (t := t) (m := m)).expectation
          (fun q => (SourceProjectedTag.positionLaw
            (branch := branch) (n := n) (t := t)).expectation
              (fun choices => (SourceProjectedTag.flagLaw flag).expectation
                (fun flags => (CutChildGrouping.rawLaw (C := C)
                  (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).expectation
                    (F q choices flags)))) := by
  rw [SourceQuestionRawSwap.originalLaw_expectation rows clauses designated flag
    (fun q choices raw =>
      let observed := observe rows clauses designated q choices raw
      F q choices observed.1 observed.2)]
  apply FiniteDistribution.expectation_congr
  intro q
  apply FiniteDistribution.expectation_congr
  intro choices
  exact kernel_expectation rows clauses designated flag q choices (F q choices)

end
end PerfectCompleteness.SourcePhysicalChildExpectation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalReplay

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)

theorem fillChild_heq (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h))
    (block : CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i) :
    HEq (fillChild rows repeats p outside inside i block) block :=
  cast_heq _ _

end
end PerfectCompleteness.CleanPhysicalReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutScalarProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionLowerForms

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

section Casts

variable {branch : Nat → Nat} {height t : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat)
  {source target : Slots branch (height + 1) → Fin t → MixedSupport.Slot}

theorem rawCast_law (h : source = target) :
    (CutChildGrouping.rawLaw (C := C) source rows).pushforward (rawCast rows h) =
      CutChildGrouping.rawLaw (C := C) target rows := by
  cases h
  exact FiniteDistribution.pushforward_id _

end Casts

end
end PerfectCompleteness.SourceQuestionLowerForms

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_SourceQuestionPhysicalCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPhysicalCollision

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple
    (branch := branch) (n := height) (t := t))
  (direction : BucketSampler.Direction (rows (height + 1)))
  (cutoff : Nat)
  (table : SourceQuestionLowerForms.UpperTable (rows := rows)
    path outside clauses upper level (adviceRows := adviceRows) q)

theorem collision_eq_probability
    (flags : SourceProjectedTag.Flags (branch := branch) (n := height)) :
    SourceQuestionPhysicalHigh.collision path outside placeholder clauses designated
        q choices flags upper level d hbranch A exterior direction cutoff table =
      (CutChildGrouping.rawLaw
        (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).probability
          (rawEvent path outside placeholder clauses designated upper level d hbranch A exterior
            q choices direction cutoff table flags) := by
  let event : LowerCutPair.Raw rows repeats path
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags) →
      Bool := fun raw =>
    LowerProjectedFiberAverage.collision
      (SourceQuestionPhysicalHigh.originalSlots path outside clauses q)
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)
      (SourceQuestionPhysicalHigh.projection path outside clauses designated q choices flags)
      upper level hbranch d A cutoff table
      (LowerCutPair.arraysPair rows repeats path
        (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)
        (SourceQuestionPhysicalHigh.exteriorAt path outside placeholder clauses designated
          q choices flags exterior) direction raw)
  have hlaw :
      (CutChildGrouping.rawLaw
        (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
        (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).pushforward
          (SourceQuestionPairPullback.rawAtCut rows repeats path outside
            (SourceProjectedTag.mixedInside clauses designated q choices flags)) =
        CutChildGrouping.rawLaw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (WholeCutGrouping.cutSlots path
            (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated
              q choices flags)) rows :=
    SourceQuestionLowerForms.rawCast_law rows
      (CleanPhysicalReplay.cutSlots_fill path outside
        (SourceProjectedTag.mixedInside clauses designated q choices flags)).symm
  exact (congrArg (fun μ : FiniteDistribution (LowerCutPair.Raw rows repeats path
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated q choices flags)) =>
        μ.probability event) hlaw).symm.trans
    (FiniteDistribution.probability_pushforward _ _ event)

theorem flags_collision_eq_kernels
    (flag : Fin (branch height) → FiniteDistribution Bool) :
    (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
      SourceQuestionPhysicalHigh.collision path outside placeholder clauses designated
        q choices flags upper level d hbranch A exterior direction cutoff table) =
      (SourceQuestionRawSwap.kernelLaw
        (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
        rows clauses designated flag q choices).probability (fun raw =>
          let observed := SourcePhysicalTaggedChildren.observe rows clauses designated
            (SourceQuestionKernelJoint.sources designated q choices) raw
          rawEvent path outside placeholder clauses designated upper level d hbranch A exterior
            q choices direction cutoff table observed.1 observed.2) := by
  let event :
      (Σ flags : SourceProjectedTag.Flags (branch := branch) (n := height),
        CutChildGrouping.Raw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (SourcePhysicalTaggedChildren.slots clauses designated
            (SourceQuestionKernelJoint.sources designated q choices) flags) rows) → Bool :=
    fun observed => rawEvent path outside placeholder clauses designated upper level d hbranch A
      exterior q choices direction cutoff table observed.1 observed.2
  have h := congrArg (fun μ : FiniteDistribution
      (Σ flags : SourceProjectedTag.Flags (branch := branch) (n := height),
        CutChildGrouping.Raw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (SourcePhysicalTaggedChildren.slots clauses designated
            (SourceQuestionKernelJoint.sources designated q choices) flags) rows) =>
      μ.probability event)
    (SourcePhysicalTaggedChildren.kernels_tagged
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      rows clauses designated flag (SourceQuestionKernelJoint.sources designated q choices))
  have hpush := FiniteDistribution.probability_pushforward
    (FiniteProduct.law (fun i => SourceChildKernel.kernel
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      rows clauses designated flag i (SourceQuestionKernelJoint.sources designated q choices i)))
    (SourcePhysicalTaggedChildren.observe rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices)) event
  have hsigma := CompletionSoundness.sigmaLaw_probability (FiniteProduct.law flag)
    (fun flags => CutChildGrouping.rawLaw
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (SourcePhysicalTaggedChildren.slots clauses designated
        (SourceQuestionKernelJoint.sources designated q choices) flags) rows) event
  calc
    _ = (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
        (CutChildGrouping.rawLaw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (SourceProjectedTag.mixedInside clauses designated q choices flags) rows).probability
            (rawEvent path outside placeholder clauses designated upper level d hbranch A exterior
              q choices direction cutoff table flags)) := by
      apply FiniteDistribution.expectation_congr
      intro flags
      exact collision_eq_probability path outside placeholder clauses designated upper level d
        hbranch A exterior q choices direction cutoff table flags
    _ = _ := (hpush.symm.trans (h.trans hsigma)).symm

variable
  (tables : (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m)) →
    SourceQuestionLowerForms.UpperTable (rows := rows)
      path outside clauses upper level (adviceRows := adviceRows) q)

theorem mean_collision_eq
    (flag : Fin (branch height) → FiniteDistribution Bool) :
    (SourceProjectedTag.positionLaw (branch := branch) (n := height) (t := t)).expectation
      (fun choices => (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
        SourceQuestionPhysicalHigh.collision path outside placeholder clauses designated
          q choices flags upper level d hbranch A exterior direction cutoff (tables q))) =
      (SourceProjectedTag.positionLaw (branch := branch) (n := height) (t := t)).expectation
        (fun choices => (SourceQuestionRawSwap.kernelLaw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          rows clauses designated flag q choices).probability (fun raw =>
            SourceQuestionCollisionTransport.globalRestricted path outside placeholder clauses
              upper level d hbranch A exterior tables cutoff designated q choices raw direction)) := by
  apply FiniteDistribution.expectation_congr
  intro choices
  rw [flags_collision_eq_kernels path outside placeholder clauses designated upper level d
    hbranch A exterior q choices direction cutoff (tables q) flag]
  apply congrArg (fun event => (SourceQuestionRawSwap.kernelLaw
    (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
    rows clauses designated flag q choices).probability event)
  funext raw
  exact rawEvent_observe path outside placeholder clauses designated upper level d hbranch A
    exterior q choices direction cutoff tables raw

end
end PerfectCompleteness.SourceQuestionPhysicalCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedSourcePhysicalHighLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourceHighBound

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (pDown : Path (branch parameters) (Nodes.height upper) (height + 1))
  (hproper : height + 1 < Nodes.height upper)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode ((Nodes.path upper).append pDown) =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper (height + 1) d))
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    ((Nodes.path upper).append pDown) outside placeholder)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q)
      upper (height + 1) bg → Prop)
  (density threshold : ℝ)

local instance rowSpaceFintype_r45c457_1 (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r45c457_1 (q : FixedSourceGlobalCollision.Questions
    (m := m) parameters (height := height)) :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper) :=
  LeftDecoder.dualFintype
    (V := NodeEmbedding.RowSpace
      (SourceQuestionLowerForms.slots ((Nodes.path upper).append pDown) outside clauses q) upper)
local instance directionNonempty_r45c457_1 :
    Nonempty (BucketSampler.Direction (rows parameters.plan (height + 1))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth - (height + 1)))⟩⟩
omit [NeZero m] in
theorem tag_collision_eq
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1)))
    (q : FixedSourceGlobalCollision.Questions (m := m) parameters (height := height))
    (table : SourceQuestionLowerForms.UpperTable (rows := rows parameters.plan)
      ((Nodes.path upper).append pDown) outside clauses upper (height + 1)
      (adviceRows := adviceRows) q) :
    (FixedSourcePhysicalHigh.tagLaw parameters).expectation (fun tag =>
      SourceQuestionPhysicalHigh.collision ((Nodes.path upper).append pDown) outside placeholder
        clauses designated q tag.1 tag.2 upper (height + 1) d
        (FixedLowerRawCollision.branchPositive parameters) A exterior direction
        (cutoff parameters.plan hδ) table) =
      FixedSourceGlobalCollision.localProbability parameters ((Nodes.path upper).append pDown)
        outside placeholder clauses designated upper d A exterior q table direction := by
  simpa only [FixedSourcePhysicalHigh.tagLaw, SourceProjectedTag.law,
    FiniteDistribution.expectation_product, FixedSourceGlobalCollision.localProbability,
    FixedSourceGlobalCollision.localTables, Function.update_self] using
    (SourceQuestionPhysicalCollision.mean_collision_eq ((Nodes.path upper).append pDown)
      outside placeholder clauses designated upper (height + 1) d
      (FixedLowerRawCollision.branchPositive parameters) A exterior q direction
      (cutoff parameters.plan hδ)
      (FixedSourceGlobalCollision.localTables parameters ((Nodes.path upper).append pDown)
        outside clauses upper q table) (FixedSourceGlobalCollision.flag parameters))

theorem probability_square_le (hdensity : 0 < density) :
    FixedSourcePhysicalHigh.probability parameters outside placeholder clauses designated upper pDown
        hproper d hnode A cut exterior σ useful density threshold ^ 2 ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  have h := FixedSourcePhysicalHigh.probability_square_le_collision parameters outside placeholder
    clauses designated upper pDown hproper d hnode A cut exterior σ useful density threshold
  simp_rw [tag_collision_eq] at h
  exact h.trans (FixedSourceGlobalCollision.mean_local_le parameters ((Nodes.path upper).append pDown)
    outside placeholder clauses designated upper d hnode A exterior σ useful density hdensity)

end
end PerfectCompleteness.FixedSourceHighBound

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FilledUniformSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FilledUniformSampler

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (m + 1) → Fin t → MixedSupport.Slot)

theorem childrenEquiv_heq
    (inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows)
    (i : Fin (branch m)) :
    HEq (childrenEquiv rows repeats p outside inside children i) (children i) :=
  cast_heq _ _

end
end PerfectCompleteness.FilledUniformSampler

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalRawChildren
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalRawChildren

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder inside : Slots branch (m + 1) → Fin t → MixedSupport.Slot)

theorem fillChildren_eq_childrenEquiv :
    fillChildren rows repeats p outside inside =
      (FilledUniformSampler.childrenEquiv rows repeats p outside inside : _ → _) := by
  funext children i
  exact eq_of_heq ((CleanPhysicalReplay.fillChild_heq rows repeats p outside inside i
    (children i)).trans
      (FilledUniformSampler.childrenEquiv_heq rows repeats p outside inside children i).symm)

theorem fillChildren_law :
    (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows).pushforward
        (fillChildren rows repeats p outside inside) =
      CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows := by
  rw [fillChildren_eq_childrenEquiv]
  simp only [CutChildGrouping.rawLaw, UniformLinearImage.law_uniform]
  rw [FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro children
  change 1 / (Fintype.card
      (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) : ℝ) =
    1 / (Fintype.card (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows) : ℝ)
  rw [Fintype.card_congr (FilledUniformSampler.childrenEquiv rows repeats p outside inside)]

theorem expectation_physicalTape
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (statistic : WholeCutSampler.Tape rows repeats p (CutSlotAssembly.fill p outside inside) → ℝ) :
    (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p) inside rows).expectation
        (fun children => statistic
          (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside external children)) =
      (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows).expectation
          (fun children => statistic
            ((WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm
              (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder inside external,
                children))) := by
  have h := congrArg
    (fun law : FiniteDistribution (CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) rows) =>
      law.expectation (fun children => statistic
        ((WholeCutGrouping.splitTape rows repeats p (CutSlotAssembly.fill p outside inside)).symm
          (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder inside external,
            children))))
    (fillChildren_law rows repeats p outside inside)
  rw [FiniteDistribution.expectation_pushforward] at h
  exact h

theorem expectation_lowerTape (upper : Nodes branch n)
    (pDown : Path branch (Nodes.height upper) (m + 1))
    (external : CleanPhysicalReplay.Exterior rows repeats
      ((Nodes.path upper).append pDown) outside placeholder)
    (statistic : WholeCutSampler.Tape rows repeats ((Nodes.path upper).append pDown)
      (CutSlotAssembly.fill ((Nodes.path upper).append pDown) outside inside) → ℝ) :
    (CutChildGrouping.rawLaw (C := WholeCutCalls.Index rows repeats ((Nodes.path upper).append pDown))
      inside rows).expectation (fun children => statistic
        (CleanPhysicalReplay.physicalTape rows repeats ((Nodes.path upper).append pDown)
          outside placeholder inside external children)) =
      (CutChildGrouping.rawLaw
        (C := LowerCutPair.Calls rows repeats ((Nodes.path upper).append pDown))
        (WholeCutGrouping.cutSlots ((Nodes.path upper).append pDown)
          (CutSlotAssembly.fill ((Nodes.path upper).append pDown) outside inside)) rows).expectation
        (fun children => statistic
          (LowerPhysicalFiberSuccess.tape
            (CutSlotAssembly.fill ((Nodes.path upper).append pDown) outside inside) upper pDown
            (CleanPhysicalReplay.exteriorAt rows repeats ((Nodes.path upper).append pDown)
              outside placeholder inside external) children)) :=
  expectation_physicalTape rows repeats ((Nodes.path upper).append pDown)
    outside placeholder inside external statistic

end
end PerfectCompleteness.CleanPhysicalRawChildren

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalHighAverage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalHighAverage

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

variable (hbranch : ∀ k < n, 0 < branch k)
  (hnode : WholeArrayInteriorExterior.upperNode (CleanDecoderRate.path S) =
    HierarchicalLeftDecoder.LowerNode upper (h + 1) d)
  {Original : OriginalDecoderMark.SlotFamily branch n t → Type*}
  [∀ slots, Fintype (Original slots)]
  (F : OriginalDecoderMark.Family branch rows n t Original) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (direction : BucketSampler.Direction (rows (h + 1))) (threshold : ℝ) (s : Nat)

theorem questionStatistic_expectation
    (q : PreliminarySampler.Questions branch (h + 1) t m)
    (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := h) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := h)) :
    (CutChildGrouping.rawLaw (C := CleanDecoderRate.Calls S)
      (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags) rows).expectation
        (questionStatistic S hbranch hnode F κ σ r ρ A direction threshold s q choices flags) =
      SourceQuestionPhysicalHigh.success S.outside S.placeholder S.clauses S.designated
        q choices flags upper (suffix S) (suffix_proper S) (h + 1) hbranch d hnode A S.cut σ
        (OriginalDecoderMark.mark F upper (h + 1) κ
          (SourceQuestionPhysicalHigh.originalSlots (CleanDecoderRate.path S) S.outside S.clauses q))
        ρ threshold S.exterior direction s := by
  exact CleanPhysicalRawChildren.expectation_lowerTape rows repeats S.outside S.placeholder
    (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags)
    upper (suffix S) S.exterior
    (tapeStatistic S hbranch hnode F κ σ r ρ A direction threshold s
      (SourceProjectedTag.originalSlots S.clauses q)
      (SourceProjectedTag.mixedInside S.clauses S.designated q choices flags)
      (SourceProjectedTag.projection S.clauses S.designated q choices flags))

theorem mean_probability_eq (cube : Nat) (hcube : 0 < cube) :
    (CleanDecoderPairLaw.pairLaw S σ (CleanPhysicalDecoderLaw.useful S F κ)
      r ρ A (LinearMap.ker A) (nativeDirection S hnode direction) threshold cube hcube).probability
        (fun z => DecoderRankSplit.highAgrees S hbranch s z.1 z.2) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := h + 1) (t := t) (m := m)).expectation
        (fun q => (SourceProjectedTag.positionLaw
          (branch := branch) (n := h) (t := t)).expectation
          (fun choices => (SourceProjectedTag.flagLaw
            (fun _ : Fin (branch h) => ProjectedCleanRate.projectionFlag cube hcube)).expectation
            (fun flags => SourceQuestionPhysicalHigh.success
              S.outside S.placeholder S.clauses S.designated q choices flags
              upper (suffix S) (suffix_proper S) (h + 1) hbranch d hnode A S.cut σ
              (OriginalDecoderMark.mark F upper (h + 1) κ
                (SourceQuestionPhysicalHigh.originalSlots
                  (CleanDecoderRate.path S) S.outside S.clauses q))
              ρ threshold S.exterior direction s))) := by
  rw [← CleanPhysicalHighEvent.mean_probability_eq S hbranch F κ σ r ρ A
    (LinearMap.ker A) (nativeDirection S hnode direction) threshold cube hcube s]
  have hsample := FiniteDistribution.expectation_congr (CleanDecoderRate.rawLaw S cube hcube)
    (physical_probability_eq_observed S hbranch hnode F κ σ r ρ A direction threshold s)
  refine hsample.trans ?_
  rw [show CleanDecoderRate.rawLaw S cube hcube =
    SourceChildKernel.originalLaw (C := CleanDecoderRate.Calls S) (t := t)
      rows S.clauses S.designated
      (fun _ => ProjectedCleanRate.projectionFlag cube hcube) from rfl]
  rw [SourcePhysicalChildExpectation.originalLaw_expectation rows S.clauses S.designated
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)
    (questionStatistic S hbranch hnode F κ σ r ρ A direction threshold s)]
  apply FiniteDistribution.expectation_congr
  intro q
  apply FiniteDistribution.expectation_congr
  intro choices
  apply FiniteDistribution.expectation_congr
  intro flags
  exact questionStatistic_expectation S hbranch hnode F κ σ r ρ A direction threshold s q choices flags

theorem probability_eq_tag_average (cube : Nat) (hcube : 0 < cube) :
    (CleanDecoderPairLaw.pairLaw S σ (CleanPhysicalDecoderLaw.useful S F κ)
      r ρ A (LinearMap.ker A) (nativeDirection S hnode direction) threshold cube hcube).probability
        (fun z => DecoderRankSplit.highAgrees S hbranch s z.1 z.2) =
      (PreliminarySampler.questionsLaw
        (branch := branch) (n := h + 1) (t := t) (m := m)).expectation
        (fun q => (SourceProjectedTag.law (t := t)
          (fun _ : Fin (branch h) => ProjectedCleanRate.projectionFlag cube hcube)).expectation
          (fun tag => SourceQuestionPhysicalHigh.success
            S.outside S.placeholder S.clauses S.designated q tag.1 tag.2
            upper (suffix S) (suffix_proper S) (h + 1) hbranch d hnode A S.cut σ
            (OriginalDecoderMark.mark F upper (h + 1) κ
              (SourceQuestionPhysicalHigh.originalSlots
                (CleanDecoderRate.path S) S.outside S.clauses q))
            ρ threshold S.exterior direction s)) := by
  simpa only [SourceProjectedTag.law, FiniteDistribution.expectation_product] using
    mean_probability_eq S hbranch hnode F κ σ r ρ A direction threshold s cube hcube

end
end PerfectCompleteness.CleanPhysicalHighAverage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedNativeHigh
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedStoppedDecoderContext.upper_height _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerNode_height _root_.OAI.PerfectCompleteness.FixedStoppedNativeProjection.flags_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedNativeHigh

noncomputable section

open scoped Classical
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  {upper : Nodes (branch parameters) parameters.plan.depth}
  {d : HierarchicalFrozenTables.LowerNodes upper (height + 1)}
  (S : CleanDecoderRate.Setup (branch parameters) (rows parameters.plan) (repeats parameters.plan)
    parameters.plan.depth height (sourceLength parameters.plan hδ) v m upper d)
  (hnode : WholeArrayInteriorExterior.upperNode (CleanDecoderRate.path S) =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {Original : OriginalDecoderMark.SlotFamily (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ) → Type*}
  [∀ slots, Fintype (Original slots)]
  (F : OriginalDecoderMark.Family (branch parameters) (rows parameters.plan)
    parameters.plan.depth (sourceLength parameters.plan hδ) Original)
  (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (r : Nat) (density : ℝ)
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) r)
  (threshold : ℝ)

attribute [local instance] OAI.PerfectCompleteness.FixedNativeHigh.directionNonempty
theorem flag_eq (h : Nat) :
    FixedSourceGlobalCollision.flag parameters (height := h) =
      fun _ : Fin (branch parameters h) =>
        ProjectedCleanRate.projectionFlag (parameters.cubeSize h)
          (FixedDecoderCleanRate.cubePositive parameters h) := by
  funext child
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  cases b <;>
    simp [FixedSourceGlobalCollision.flag, ProjectedCleanRate.projectionFlag,
      ProjectionPosterior.bernoulli, RepetitionRate.bernoulli,
      FixedParameters.projectionProbability, ProjectedCleanRate.projectionDensity]

theorem probability_eq_physical :
    probability parameters S hnode F κ σ r density A threshold =
      FixedSourcePhysicalHigh.probability parameters S.outside S.placeholder S.clauses S.designated
        upper (CleanPhysicalHighAverage.suffix S) (CleanPhysicalHighAverage.suffix_proper S)
        d hnode A S.cut S.exterior σ (questionUseful parameters S F κ) density threshold := by
  unfold probability FixedSourcePhysicalHigh.probability
  apply FiniteDistribution.expectation_congr
  intro direction
  rw [CleanPhysicalHighAverage.probability_eq_tag_average S
    (FixedLowerRawCollision.branchPositive parameters) hnode F κ σ r density A direction
    threshold (cutoff parameters.plan hδ) (parameters.cubeSize height)
    (FixedDecoderCleanRate.cubePositive parameters height)]
  simp only [FixedSourcePhysicalHigh.tagLaw, flag_eq]
  apply FiniteDistribution.expectation_congr
  intro q
  apply FiniteDistribution.expectation_congr
  intro tag
  rfl

theorem probability_square_le (hdensity : 0 < density) :
    probability parameters S hnode F κ σ r density A threshold ^ 2 ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  rw [probability_eq_physical]
  exact FixedSourceHighBound.probability_square_le parameters S.outside S.placeholder S.clauses
    S.designated upper (CleanPhysicalHighAverage.suffix S) (CleanPhysicalHighAverage.suffix_proper S)
    d hnode A S.cut S.exterior σ (questionUseful parameters S F κ) density threshold hdensity

end
end PerfectCompleteness.FixedNativeHigh

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedHighBound
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedHighBound

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

private theorem castDirection_eq {branch rows : Nat → Nat} {n : Nat}
    {node node' : Nodes branch n} (h : node = node')
    (a : BucketSampler.Direction (rows (Nodes.height node))) :
    ProjectedFiberRawPair.castDirection h a =
      LowerCutInstalledInput.directionCast rows h a := by
  cases h
  rfl

theorem directionMean_eq_native
    (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (A : FixedStoppedDecoderContext.Advice parameters i j pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) :
    directionMean parameters i j hij input strategy pref external A exterior =
      FixedNativeHigh.probability parameters (setup parameters i j hij input pref external exterior)
        (setup_node parameters i j hij input pref external exterior)
        (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy pref)
        (InitialParameters.useful δ) (FixedStoppedDecoderLaw.labeling parameters input strategy)
        parameters.plan.order parameters.plan.density A
        (FixedStoppedDecoderLaw.threshold parameters j) := by
  let : Nonempty (BucketSampler.Direction (FixedRows.rows parameters.plan (i.val + 1))) :=
    PreliminarySampler.directionNonempty _
      (parameters.plan.rows_pos (parameters.plan.depth - (i.val + 1)))
  let e := LowerCutInstalledInput.lowerDirectionEquiv (FixedRows.rows parameters.plan)
    (CleanDecoderRate.path (setup parameters i j hij input pref external exterior))
    (FixedStoppedDecoderContext.upper parameters i j pref) (i.val + 1)
    (FixedStoppedDecoderContext.lower parameters i j hij pref)
    (setup_node parameters i j hij input pref external exterior)
  have htransport :
      (FiniteDistribution.uniform
        (BucketSampler.Direction (FixedRows.rows parameters.plan (i.val + 1)))).pushforward e =
      FixedStoppedDirections.lowerLaw parameters i j hij pref := by
    rw [← FiniteDistribution.transport_eq_pushforward]
    exact UniformConditioning.uniform_transport e
  unfold directionMean
  rw [← htransport, FiniteDistribution.expectation_pushforward]
  unfold FixedNativeHigh.probability
  apply FiniteDistribution.expectation_congr
  intro a
  have hdirection : e a =
      ProjectedFiberRawPair.direction
        (CleanDecoderRate.path (setup parameters i j hij input pref external exterior))
        (FixedStoppedDecoderContext.upper parameters i j pref) (i.val + 1)
        (FixedStoppedDecoderContext.lower parameters i j hij pref)
        (setup_node parameters i j hij input pref external exterior) a := by
    unfold e LowerCutInstalledInput.lowerDirectionEquiv ProjectedFiberRawPair.direction
    exact (castDirection_eq _ _).symm
  rw [hdirection]
  rfl

theorem directionMean_square_le_oai
    (strategy : FixedPreliminaryGame.Strategy parameters input)
    (pref : Prefixes parameters i j)
    (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
    (A : FixedStoppedDecoderContext.Advice parameters i j pref)
    (exterior : FixedStoppedDecoderContext.Exterior parameters i j hij input pref external) :
    directionMean parameters i j hij input strategy pref external A exterior ^ 2 ≤
      FixedRankContradiction.gamma parameters (j.val + 1) ^ 2 / 8 + 2 * parameters.accuracy := by
  rw [directionMean_eq_native]
  simpa only [WholeArrayInteriorExterior.upperNode_height] using
    FixedNativeHigh.probability_square_le parameters
      (setup parameters i j hij input pref external exterior)
      (setup_node parameters i j hij input pref external exterior)
      (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy pref)
      (InitialParameters.useful δ) (FixedStoppedDecoderLaw.labeling parameters input strategy)
      parameters.plan.order parameters.plan.density A
      (FixedStoppedDecoderLaw.threshold parameters j) parameters.plan.density_pos

end
end PerfectCompleteness.FixedStoppedHighBound

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedHighBound.directionMean_square_le_oai := @OAI.PerfectCompleteness.FixedStoppedHighBound.directionMean_square_le_oai
