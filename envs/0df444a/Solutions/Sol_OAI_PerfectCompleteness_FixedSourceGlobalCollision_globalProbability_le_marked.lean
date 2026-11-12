-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedSourceGlobalCollision.globalProbability_le_marked
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:21:46.459688+00:00
-- url     : https://prove2.me/submissions/446c1bf6-bd12-462e-a06d-913f92ff6eb0

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderTableCoupling
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DecoderTableCoupling

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]

theorem probability_eq_expectation {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (event : X → Bool) :
    μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite,
    mul_one, mul_zero]

end
end PerfectCompleteness.DecoderTableCoupling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_ChildUnmarkedSpace
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
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

private theorem projection_self_map (s : MixedSupport.Slot)
    (p : MixedSupport.Projection s s) (x : s.Domain) : p.map x = x := by
  cases s <;> cases p <;> rfl

private theorem sourceProjection_self
    {slots : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (slots s k))
    (x : Domain slots) : sourceProjection p x = x := by
  funext s k
  exact projection_self_map (slots s k) (p s k) (x s k)

theorem squarePullback_surjective_of_eq
    {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (heq : projected = slots) : Function.Surjective (ChildBlockProjection.squarePullback p) := by
  subst projected
  intro v
  refine ⟨v, ?_⟩
  apply Subtype.ext
  funext x
  change v.val (sourceProjection p x) = v.val x
  rw [sourceProjection_self]

theorem childMap_pullback
    {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) (v : squareSpace (H (childSlots projected i))) :
    childMap slots i
        (ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection p i) v) =
      HPullback p (childMap projected i v) := by
  apply Subtype.ext
  funext x
  rfl

theorem childMap_mem_projected_range
    {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (i : Fin (branch n)) (heq : childSlots projected i = childSlots slots i)
    (v : squareSpace (H (childSlots slots i))) :
    childMap slots i v ∈ LinearMap.range (HPullback p) := by
  obtain ⟨w, rfl⟩ := squarePullback_surjective_of_eq
    (ChildAssemblyProjection.childProjection p i) heq v
  exact ⟨childMap projected i w, (childMap_pullback p i w).symm⟩

theorem space_le_projected_range
    {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (mask : Fin (branch n) → Bool)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hkeep : ∀ i, mask i = false → childSlots projected i = childSlots slots i) :
    space slots mask ≤ LinearMap.range (HPullback p) := by
  apply iSup_le
  intro i
  apply iSup_le
  intro hi
  rintro _ ⟨v, rfl⟩
  exact childMap_mem_projected_range p i (hkeep i hi) v

end
end PerfectCompleteness.ChildUnmarkedSpace

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceChildKernelLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ProjectedNativeCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedNativeCollision

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
  (p : ∀ leaf k, MixedSupport.Projection (slots leaf k) (projected leaf k))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

section SourceKernel

variable {rows : Nat → Nat} {v m k : Nat} {C : Type*} [Fintype C]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch k) → Slots branch k)
  (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
  (raw : (i : Fin (branch k)) →
    SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)

theorem parent_childSlots_of_unmarked (i : Fin (branch k))
    (hi : SourceChildKernel.rawProjected rows clauses designated i (raw i) = false) :
    childSlots (SourceChildKernel.parentRightSlots rows clauses designated sources raw) i =
      childSlots (SourceChildKernel.parentLeftSlots clauses designated sources) i := by
  funext leaf a
  change SourceChildKernel.mixedSlots clauses designated i (sources i)
      (SourceChildKernel.rawProjected rows clauses designated i (raw i)) leaf a =
    SourceChildKernel.nativeSlots clauses designated i (sources i) leaf a
  rw [hi]
  rfl

theorem parent_unmarked_le_range :
    ChildUnmarkedSpace.space
      (SourceChildKernel.parentLeftSlots clauses designated sources)
      (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)) ≤
      LinearMap.range (HPullback
        (SourceChildKernel.parentProjection rows clauses designated sources raw)) := by
  apply ChildUnmarkedSpace.space_le_projected_range
  exact parent_childSlots_of_unmarked clauses designated sources raw

end SourceKernel

end
end PerfectCompleteness.ProjectedNativeCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionUnmarkedRange
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionUnmarkedRange

open scoped Classical
open RecursiveSpaces TreeSourceSpaces SourceChildKernel

noncomputable section

variable {branch : Nat → Nat} {height t v m : Nat}

private theorem unmarked_range_cast
    {left native right : Slots branch (height + 1) → Fin t → MixedSupport.Slot}
    (h : left = native)
    (p : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (mask : Fin (branch height) → Bool)
    (hin : ChildUnmarkedSpace.space left mask ≤ LinearMap.range (HPullback p)) :
    ChildUnmarkedSpace.space native mask ≤
      LinearMap.range (HPullback (CutNativeForms.projectionCast h rfl p)) := by
  cases h
  exact hin

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (q : SourceChildMarkedLaw.Questions (branch := branch) (n := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := height) (t := t))

variable {C : Type*} [Fintype C]
  (raw : (i : Fin (branch height)) → Raw (C := C) (t := t) rows clauses designated i)

theorem unmarked_le_range :
    ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q)
        (fun i => rawProjected rows clauses designated i (raw i)) ≤
      LinearMap.range (HPullback (projection rows clauses designated q choices raw)) := by
  exact unmarked_range_cast (leftSlots_eq clauses designated q choices)
    (parentProjection rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)
    (fun i => rawProjected rows clauses designated i (raw i))
    (ProjectedNativeCollision.parent_unmarked_le_range clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)

end
end PerfectCompleteness.SourceQuestionUnmarkedRange

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionAssembly
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutProjectionAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces MixedSupport

variable {branch : Nat → Nat} {n m t : Nat}

private theorem dite_heq_of_pos {α β : Type} {P : Prop} [Decidable P]
    (f : P → α) (g : ¬ P → α) (b : β) (hP : P)
    (h : HEq (f hP) b) : HEq (dite P f g) b := by
  rw [dite_eq_left hP]
  exact h

theorem fillProjection_at_cut (p : Path branch n m)
    (outside : Slots branch n → Fin t → Slot)
    (left right : Slots branch m → Fin t → Slot)
    (q : ∀ s k, Projection (left s k) (right s k))
    (s : Slots branch m) (k : Fin t) :
    HEq (fillProjection p outside left right q (p.slotEmbedding s) k) (q s k) := by
  revert outside left right q s k
  induction p with
  | refl _ => intros; rfl
  | step i p ih =>
      intro outside left right q s k
      refine @dite_heq_of_pos _ _ (i = i) _ _ _ (q s k) rfl ?_
      exact (castProjection_heq _ _ _).trans
        (ih (fun j => outside (i, j)) left right q s k)

theorem fillProjection_at_cut_cast (p : Path branch n m)
    (outside : Slots branch n → Fin t → Slot)
    (left right : Slots branch m → Fin t → Slot)
    (q : ∀ s k, Projection (left s k) (right s k))
    (s : Slots branch m) (k : Fin t) :
    castProjection
      (congrFun (CutSlotAssembly.fill_at_cut p outside left s) k)
      (congrFun (CutSlotAssembly.fill_at_cut p outside right s) k)
      (fillProjection p outside left right q (p.slotEmbedding s) k) = q s k := by
  apply eq_of_heq
  exact (castProjection_heq _ _ _).trans (fillProjection_at_cut p outside left right q s k)

end
end PerfectCompleteness.CutProjectionAssembly

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutScalarProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutScalarProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem scalarEquiv_HPullback :
    {n m : Nat} → (p : Path branch n (m + 1)) →
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot) →
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) →
    (f : H (subtreeSlots p projected)) →
    LowerCutNodeCoordinates.scalarEquiv p slots
        (HPullback (fun s k => q (p.slotEmbedding s) k) f) =
      HPullback (ChildBlockProjection.nodeProjection q (upperNode p))
        (LowerCutNodeCoordinates.scalarEquiv p projected f)
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .step i p, slots, projected, q, f =>
      scalarEquiv_HPullback p (childSlots slots i) (childSlots projected i)
        (fun s k => q (i, s) k) f

theorem projectionCast_apply
    {a b c d : Slots branch m → Fin t → MixedSupport.Slot}
    (hab : a = b) (hcd : c = d)
    (q : ∀ s k, MixedSupport.Projection (a s k) (c s k))
    (s : Slots branch m) (k : Fin t) :
    CutNativeForms.projectionCast hab hcd q s k =
      CutProjectionAssembly.castProjection
        (congrFun (congrFun hab s) k) (congrFun (congrFun hcd s) k) (q s k) := by
  cases hab
  cases hcd
  rfl

theorem projectionCast_fill (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) :
    CutNativeForms.projectionCast
        (CleanPhysicalReplay.cutSlots_fill p outside left)
        (CleanPhysicalReplay.cutSlots_fill p outside right)
        (fun s k => CutProjectionAssembly.fillProjection p outside left right q
          (p.slotEmbedding s) k) = q := by
  funext s k
  rw [projectionCast_apply]
  exact CutProjectionAssembly.fillProjection_at_cut_cast p outside left right q s k

theorem inverse_spaceCast_HPullback
    {a b c d : Slots branch m → Fin t → MixedSupport.Slot}
    (hab : a = b) (hcd : c = d)
    (q : ∀ s k, MixedSupport.Projection (a s k) (c s k)) (f : H d) :
    CutNativeForms.spaceCast hab.symm
        (HPullback (CutNativeForms.projectionCast hab hcd q) f) =
      HPullback q (CutNativeForms.spaceCast hcd.symm f) := by
  cases hab
  cases hcd
  rfl

theorem fill_spaceCast_HPullback (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) (f : H right) :
    CutNativeForms.spaceCast (CleanPhysicalReplay.cutSlots_fill p outside left).symm
        (HPullback q f) =
      HPullback
        (fun s k => CutProjectionAssembly.fillProjection p outside left right q
          (p.slotEmbedding s) k)
        (CutNativeForms.spaceCast
          (CleanPhysicalReplay.cutSlots_fill p outside right).symm f) := by
  have h := inverse_spaceCast_HPullback
    (CleanPhysicalReplay.cutSlots_fill p outside left)
    (CleanPhysicalReplay.cutSlots_fill p outside right)
    (fun s k => CutProjectionAssembly.fillProjection p outside left right q
      (p.slotEmbedding s) k) f
  rw [projectionCast_fill] at h
  exact h

theorem nodeEquiv_HPullback
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    {a b : Nodes branch n} (hab : a = b) (f : H (nodeSlots projected a)) :
    nodeEquiv slots hab (HPullback (ChildBlockProjection.nodeProjection q a) f) =
      HPullback (ChildBlockProjection.nodeProjection q b) (nodeEquiv projected hab f) := by
  cases hab
  rfl

theorem spaceEquiv_HPullback (p : Path branch n (m + 1))
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) (level : Nat)
    (d : HierarchicalFrozenTables.LowerNodes upper level)
    (hnode : upperNode p = HierarchicalLeftDecoder.LowerNode upper level d)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (f : H (subtreeSlots p projected)) :
    LowerCutDecoderForm.spaceEquiv p slots upper level d hnode
        (HPullback (fun s k => q (p.slotEmbedding s) k) f) =
      HPullback (ChildBlockProjection.nodeProjection q
        (HierarchicalLeftDecoder.LowerNode upper level d))
        (LowerCutDecoderForm.spaceEquiv p projected upper level d hnode f) := by
  change nodeEquiv slots hnode
      (LowerCutNodeCoordinates.scalarEquiv p slots
        (HPullback (fun s k => q (p.slotEmbedding s) k) f)) =
    HPullback (ChildBlockProjection.nodeProjection q
      (HierarchicalLeftDecoder.LowerNode upper level d))
      (nodeEquiv projected hnode (LowerCutNodeCoordinates.scalarEquiv p projected f))
  rw [scalarEquiv_HPullback, nodeEquiv_HPullback]

theorem spaceEquiv_fill_HPullback (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (upper : Nodes branch n) (level : Nat)
    (d : HierarchicalFrozenTables.LowerNodes upper level)
    (hnode : upperNode p = HierarchicalLeftDecoder.LowerNode upper level d)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k)) (f : H right) :
    LowerCutDecoderForm.spaceEquiv p (CutSlotAssembly.fill p outside left)
        upper level d hnode
        (CutNativeForms.spaceCast (CleanPhysicalReplay.cutSlots_fill p outside left).symm
          (HPullback q f)) =
      HPullback (ChildBlockProjection.nodeProjection
        (CutProjectionAssembly.fillProjection p outside left right q)
        (HierarchicalLeftDecoder.LowerNode upper level d))
        (LowerCutDecoderForm.spaceEquiv p (CutSlotAssembly.fill p outside right)
          upper level d hnode
          (CutNativeForms.spaceCast
            (CleanPhysicalReplay.cutSlots_fill p outside right).symm f)) := by
  rw [fill_spaceCast_HPullback]
  exact spaceEquiv_HPullback p _ _ upper level d hnode _ _

end
end PerfectCompleteness.LowerCutScalarProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutFormCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutFormCollision

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n height t : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (inside : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)

private theorem formCast_apply_inverse
    {source target : Slots branch (height + 1) → Fin t → MixedSupport.Slot}
    (h : source = target) (F : ChildBilinearCollisionTransfer.ParentForm source)
    (f g : H target) :
    CutNativeForms.formCast h F f g =
      F (CutNativeForms.spaceCast h.symm f) (CutNativeForms.spaceCast h.symm g) := by
  cases h
  rfl

theorem nativeForm_apply
    (answer : HierarchicalDecoderTables.Answer
      (CutSlotAssembly.fill path outside inside) upper level d) (f g : H inside) :
    nativeForm path outside inside upper level d hnode answer f g =
      OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (CutSlotAssembly.fill path outside inside) upper level d) answer
        (nativeScalar path outside inside upper level d hnode f)
        (nativeScalar path outside inside upper level d hnode g) := by
  unfold nativeForm
  rw [formCast_apply_inverse]
  rfl

variable (projected : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (projection : ∀ s k, MixedSupport.Projection (inside s k) (projected s k))

theorem nativeScalar_HPullback (f : H projected) :
    nativeScalar path outside inside upper level d hnode (HPullback projection f) =
      HPullback (ChildBlockProjection.nodeProjection
        (CutProjectionAssembly.fillProjection path outside inside projected projection)
        (HierarchicalLeftDecoder.LowerNode upper level d))
        (nativeScalar path outside projected upper level d hnode f) :=
  LowerCutScalarProjection.spaceEquiv_fill_HPullback path outside inside projected
    upper level d hnode projection f

theorem restricted_on_native
    (answer₀ answer₁ : Option (HierarchicalDecoderTables.Answer
      (CutSlotAssembly.fill path outside inside) upper level d))
    (U : Submodule F2 (H inside)) (hU : U ≤ LinearMap.range (HPullback projection))
    (hcollision : BilinearCollisionTransfer.restrictedCollision
      (answer₀.map (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (CutSlotAssembly.fill path outside inside) upper level d)))
      (answer₁.map (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH
          (CutSlotAssembly.fill path outside inside) upper level d)))
      (LinearMap.range (HPullback (ChildBlockProjection.nodeProjection
        (CutProjectionAssembly.fillProjection path outside inside projected projection)
        (HierarchicalLeftDecoder.LowerNode upper level d)))) = true) :
    BilinearCollisionTransfer.restrictedCollision
      (answer₀.map (nativeForm path outside inside upper level d hnode))
      (answer₁.map (nativeForm path outside inside upper level d hnode)) U = true := by
  obtain ⟨F, G, hF, hG, heq⟩ := of_decide_eq_true hcollision
  cases answer₀ with
  | none => cases hF
  | some a₀ =>
      cases answer₁ with
      | none => cases hG
      | some a₁ =>
          have hF' := Option.some.inj hF
          have hG' := Option.some.inj hG
          rw [← hF', ← hG'] at heq
          apply decide_eq_true
          refine ⟨nativeForm path outside inside upper level d hnode a₀,
            nativeForm path outside inside upper level d hnode a₁, rfl, rfl, ?_⟩
          intro f hf g hg
          rw [nativeForm_apply, nativeForm_apply]
          obtain ⟨f', hf'⟩ := hU hf
          obtain ⟨g', hg'⟩ := hU hg
          have hfmem : nativeScalar path outside inside upper level d hnode f ∈
              LinearMap.range (HPullback (ChildBlockProjection.nodeProjection
                (CutProjectionAssembly.fillProjection path outside inside projected projection)
                (HierarchicalLeftDecoder.LowerNode upper level d))) := by
            refine ⟨nativeScalar path outside projected upper level d hnode f', ?_⟩
            rw [← nativeScalar_HPullback, hf']
          have hgmem : nativeScalar path outside inside upper level d hnode g ∈
              LinearMap.range (HPullback (ChildBlockProjection.nodeProjection
                (CutProjectionAssembly.fillProjection path outside inside projected projection)
                (HierarchicalLeftDecoder.LowerNode upper level d))) := by
            refine ⟨nativeScalar path outside projected upper level d hnode g', ?_⟩
            rw [← nativeScalar_HPullback, hg']
          exact heq _ hfmem _ hgmem

end
end PerfectCompleteness.LowerCutFormCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_SourceQuestionCollisionTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionCollisionTransport

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (tables : (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m)) →
    SourceQuestionLowerForms.UpperTable (rows := rows) path outside clauses
      upper level (adviceRows := adviceRows) q)
  (cutoff : Nat)

variable
  (designated : Fin (branch height) → Slots branch height)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := height) (t := t))
  (raw : (i : Fin (branch height)) →
    SourceChildKernel.Raw (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (t := t) rows clauses designated i)

theorem globalRestricted_imp_native
    (hnode : WholeArrayInteriorExterior.upperNode path =
      HierarchicalLeftDecoder.LowerNode upper level d)
    (direction : BucketSampler.Direction (rows (height + 1)))
    (hcollision : globalRestricted path outside placeholder clauses upper level d hbranch A
      exterior tables cutoff designated q choices raw direction = true) :
    BilinearCollisionTransfer.restrictedCollision
      (SourceQuestionLowerForms.first path outside placeholder clauses upper level d hnode hbranch A
        exterior tables cutoff q (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2)
      (SourceQuestionLowerForms.second path outside placeholder clauses upper level d hnode hbranch A
        exterior tables cutoff direction q
        (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2)
      (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q)
        (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).1) = true := by
  have hU : ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q)
        (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).1 ≤
      LinearMap.range (HPullback
        (SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw)) :=
    SourceQuestionUnmarkedRange.unmarked_le_range rows clauses designated q choices raw
  have h := LowerCutFormCollision.restricted_on_native path outside
    (SourceChildMarkedLaw.questionSlots clauses q) upper level d hnode
    (SourceChildKernel.parentRightSlots rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)
    (SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw)
    (firstAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
      q (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2)
    (secondAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
      direction q (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2)
    (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q)
      (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).1)
    hU hcollision
  have hmapper :
      LowerCutFormCollision.nativeForm path outside (SourceChildMarkedLaw.questionSlots clauses q)
          upper level d hnode =
        (fun answer : HierarchicalDecoderTables.Answer
            (SourceQuestionLowerForms.slots path outside clauses q) upper level d =>
          CutNativeForms.formCast (SourceQuestionLowerForms.cutSlots_eq path outside clauses q)
            (LowerCutDecoderForm.form path (SourceQuestionLowerForms.slots path outside clauses q)
              upper level d hnode answer)) := by
    funext answer
    rfl
  have hfirst (record : SourceQuestionLowerForms.Raw
      (rows := rows) (repeats := repeats) path clauses q) :
      SourceQuestionLowerForms.first path outside placeholder clauses upper level d hnode hbranch A
          exterior tables cutoff q record =
        (firstAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
          q record).map (LowerCutFormCollision.nativeForm path outside
            (SourceChildMarkedLaw.questionSlots clauses q) upper level d hnode) := by
    change ((firstAnswer path outside placeholder clauses upper level d hbranch A exterior tables
      cutoff q record).map
        (LowerCutDecoderForm.form path (SourceQuestionLowerForms.slots path outside clauses q)
          upper level d hnode)).map
        (CutNativeForms.formCast (SourceQuestionLowerForms.cutSlots_eq path outside clauses q)) = _
    rw [Option.map_map]
    exact congrArg (fun mapper => (firstAnswer path outside placeholder clauses upper level d
      hbranch A exterior tables cutoff q record).map mapper) hmapper.symm
  have hsecond (record : SourceQuestionLowerForms.Raw
      (rows := rows) (repeats := repeats) path clauses q) :
      SourceQuestionLowerForms.second path outside placeholder clauses upper level d hnode hbranch A
          exterior tables cutoff direction q record =
        (secondAnswer path outside placeholder clauses upper level d hbranch A exterior tables cutoff
          direction q record).map (LowerCutFormCollision.nativeForm path outside
            (SourceChildMarkedLaw.questionSlots clauses q) upper level d hnode) := by
    change ((secondAnswer path outside placeholder clauses upper level d hbranch A exterior tables
      cutoff direction q record).map
        (LowerCutDecoderForm.form path (SourceQuestionLowerForms.slots path outside clauses q)
          upper level d hnode)).map
        (CutNativeForms.formCast (SourceQuestionLowerForms.cutSlots_eq path outside clauses q)) = _
    rw [Option.map_map]
    exact congrArg (fun mapper => (secondAnswer path outside placeholder clauses upper level d
      hbranch A exterior tables cutoff direction q record).map mapper) hmapper.symm
  rw [hfirst, hsecond]
  exact h

end
end PerfectCompleteness.SourceQuestionCollisionTransport

end

section

namespace PerfectCompleteness.FixedSourceGlobalCollision

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height v m : Nat} [NeZero m]
  (path : Path (branch parameters) parameters.plan.depth (height + 1))
  (outside : Slots (branch parameters) parameters.plan.depth →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (placeholder : Slots (branch parameters) (height + 1) →
    Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)
  {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior (rows parameters.plan) (repeats parameters.plan)
    path outside placeholder)

local instance rowSpaceFintype_ref4fcc_1 (q : Questions (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.FixedSourceGlobalCollision.upperAnswerFintype
attribute [local instance] OAI.PerfectCompleteness.FixedSourceGlobalCollision.tableFintype
attribute [local instance] OAI.PerfectCompleteness.FixedSourceGlobalCollision.directionNonempty
theorem nativeProbability_eq_marked
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) :
    nativeProbability parameters path outside placeholder clauses designated upper d hnode A
        exterior tables direction =
      FixedSourceLowerCollision.markedProbability parameters path outside placeholder clauses
        designated upper d hnode A exterior tables direction := by
  let event (q : Questions (m := m) parameters (height := height))
      (choices : Choice parameters (height := height))
      (raw : SourceChildKernelJoint.RawTuple
        (C := FixedSourceChildCollision.Calls parameters path)
        (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses designated) : Bool :=
    let record := SourceChildMarkedLaw.markedBlocks
      (rows parameters.plan) clauses designated q choices raw
    BilinearCollisionTransfer.restrictedCollision
      (FixedSourceLowerCollision.first parameters path outside placeholder clauses
        upper d hnode A exterior tables q record.2)
      (FixedSourceLowerCollision.second parameters path outside placeholder clauses
        upper d hnode A exterior tables direction q record.2)
      (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses q) record.1)
  have hlaw : FixedSourceChildCollision.markedLaw parameters path clauses designated =
      SourceChildKernel.originalLaw
        (C := FixedSourceChildCollision.Calls parameters path)
        (t := sourceLength parameters.plan hδ)
        (rows parameters.plan) clauses designated (flag parameters) := rfl
  have hevent : FixedSourceChildCollision.restrictedEvent parameters path clauses designated
      (FixedSourceLowerCollision.first parameters path outside placeholder clauses
        upper d hnode A exterior tables)
      (FixedSourceLowerCollision.second parameters path outside placeholder clauses
        upper d hnode A exterior tables direction) =
      (fun sample => event
        (SourceQuestionRawSwap.insideQuestions (rows parameters.plan) clauses designated sample)
        (SourceQuestionRawSwap.positions (rows parameters.plan) clauses designated sample)
        (SourceQuestionRawSwap.raw (rows parameters.plan) clauses designated sample)) := by
    funext sample
    rfl
  unfold nativeProbability FixedSourceLowerCollision.markedProbability
  rw [hlaw, hevent]
  simp_rw [DecoderTableCoupling.probability_eq_expectation]
  exact (SourceQuestionRawSwap.originalLaw_expectation
    (C := FixedSourceChildCollision.Calls parameters path)
    (rows parameters.plan) clauses designated (flag parameters)
    (fun q choices raw => if event q choices raw then 1 else 0)).symm

theorem globalProbability_le_marked_oai
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) :
    globalProbability parameters path outside placeholder clauses designated upper d A
        exterior tables direction ≤
      FixedSourceLowerCollision.markedProbability parameters path outside placeholder clauses
        designated upper d hnode A exterior tables direction := by
  rw [← nativeProbability_eq_marked]
  apply SmallBias.expectation_mono
  intro q
  apply SmallBias.expectation_mono
  intro choices
  apply FiniteDistribution.probability_mono
  intro raw hcollision
  exact SourceQuestionCollisionTransport.globalRestricted_imp_native path outside placeholder clauses
    upper (height + 1) d (FixedLowerRawCollision.branchPositive parameters) A exterior tables
    (cutoff parameters.plan hδ) designated q choices raw hnode direction hcollision

end
end PerfectCompleteness.FixedSourceGlobalCollision

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedSourceGlobalCollision.globalProbability_le_marked_oai := @OAI.PerfectCompleteness.FixedSourceGlobalCollision.globalProbability_le_marked_oai
