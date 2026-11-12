-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedUpperProbability.pairedVariation_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:29.625368+00:00
-- url     : https://prove2.me/submissions/c74a8694-c881-4553-aed6-78be329532f5

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
import Theorems.Thm_OAI_PerfectCompleteness_FixedUpperCutTriangle_original_reference_lt
import Theorems.Thm_OAI_PerfectCompleteness_StoppedSourcePairLaw_prefix_pair_law
import Theorems.Thm_OAI_PerfectCompleteness_StoppedUsefulPairLaw_actualPair_law

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CommonProductVariationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ConditionalVariation

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness

noncomputable section

variable {S : Type*} [Fintype S] {Ω : S → Type*} [∀ s, Fintype (Ω s)]

theorem sigma_totalVariation (μ : FiniteDistribution S)
    (P Q : (s : S) → FiniteDistribution (Ω s)) :
    (sigmaLaw μ P).totalVariation (sigmaLaw μ Q) =
      μ.expectation (fun s => (P s).totalVariation (Q s)) := by
  change (∑ z : Σ s, Ω s,
    |μ.weight z.1 * (P z.1).weight z.2 - μ.weight z.1 * (Q z.1).weight z.2|) / 2 =
      ∑ s, μ.weight s * ((∑ x : Ω s, |(P s).weight x - (Q s).weight x|) / 2)
  rw [Fintype.sum_sigma, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (μ.nonnegative s)]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_assoc]

end
end PerfectCompleteness.ConditionalVariation


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedUsefulPairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedUsefulPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {N j i t : Nat}

attribute [local instance] OAI.PerfectCompleteness.StoppedUsefulPairLaw.rowSpaceFintype
attribute [local instance] OAI.PerfectCompleteness.StoppedUsefulPairLaw.backgroundFintype
theorem stoppedProjectedPair_law (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j (i + 1)) (hproper : i + 1 < j + 1)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    (actualLaw rows repeats p chosen q right hrows).pushforward
        (UpperScalarCutProjection.stoppedProjectedPair rows repeats p (.step chosen q) hproper
          native right projection) =
      HierarchicalUsefulCollision.pairLaw native (upperNode p)
        (externalLaw rows repeats p chosen q right)
        (background rows repeats p chosen q native right projection)
        (scalarLaw rows repeats p chosen q native right projection)
        (by simpa only [upperNode_height] using hrows) :=
  actualPair_law rows repeats p chosen q native right projection hrows

end
end PerfectCompleteness.StoppedUsefulPairLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedCoarseLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedPairMean

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}

attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedPairMean.backgroundFintype
local instance rowSpaceFintype_r767f39_1 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
theorem proper_pair_law (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hij : i < j)
    (native right : Slots branch n → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    ((StoppedUsefulPairLaw.directionLaw rows j hrows).product
      ((WholeArraySampler.tapeLaw rows repeats (p.append r) right).product
        (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p right))))).pushforward
          (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r
            (Nat.succ_lt_succ hij) native right projection) =
      HierarchicalUsefulCollision.pairLaw native (upperNode p)
        (StoppedUsefulPairLaw.externalLaw rows repeats p (StoppedPathHead.child hij r)
          (StoppedPathHead.tail hij r) right)
        (StoppedUsefulPairLaw.background rows repeats p (StoppedPathHead.child hij r)
          (StoppedPathHead.tail hij r) native right projection)
        (StoppedUsefulPairLaw.scalarLaw rows repeats p (StoppedPathHead.child hij r)
          (StoppedPathHead.tail hij r) native right projection)
        (by simpa only [upperNode_height] using hrows) := by
  cases r with
  | refl => exact False.elim ((Nat.lt_irrefl _) hij)
  | step child q =>
      exact StoppedUsefulPairLaw.stoppedProjectedPair_law rows repeats p child q
        (Nat.succ_lt_succ hij) native right projection hrows

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedPairMean.nativeBackgroundFintype
local instance nativeRowSpaceFintype_r767f39_1 :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _
theorem fixedPair_eq (base : StoppedProjectedBucketIndex.Base
    (branch := branch) (i := i) (j := j) (t := t)) :
    fixedPair clauses rows repeats hupper hij designated hrows o base =
      HierarchicalUsefulCollision.pairLaw (StoppedProjectedExperiment.nativeSlots clauses o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedBuckets.exteriorLaw clauses rows repeats hupper hij designated hrows o base)
        (fun external => StoppedProjectedBuckets.background clauses rows repeats hupper hij
          designated hrows o ⟨base, external⟩)
        (fun external => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij
          designated hrows o ⟨base, external⟩)
        (StoppedProjectedBuckets.rows_positive rows hupper hrows o) :=
  proper_pair_law rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedBuckets.lowerPath (n := n) rows hij hrows base) hij
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
    (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base) (hrows j)

theorem pairedLaw_eq_mixture (hbranch : ∀ k < j + 1, 0 < branch k)
    (flag : Fin (branch i) → FiniteDistribution Bool)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) :
    HierarchicalAdviceFromBuckets.pairedLaw
        (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o hbranch flag σ)
        (StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
        (StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
        (StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
        (StoppedProjectedBuckets.rows_positive rows hupper hrows o) =
      (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).mixture
        (fixedPair clauses rows repeats hupper hij designated hrows o) := by
  apply SigmaObservation.eq_of_probability_eq
    (X := HierarchicalAgreementMean.PairRecord (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o))
  intro event
  change (HierarchicalUsefulCollision.pairLaw
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch flag)
      (StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
      (StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
      (StoppedProjectedBuckets.rows_positive rows hupper hrows o)).probability event =
    ((StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).mixture
      (fixedPair clauses rows repeats hupper hij designated hrows o)).probability event
  rw [HierarchicalUsefulCollision.pairLaw, FiniteDistribution.probability_pushforward,
    HierarchicalUsefulCollision.law, CompletionSoundness.sigmaLaw_probability,
    StoppedProjectedBuckets.externalLaw, CandidateCoupling.expectation_sigmaLaw,
    FiniteDistribution.probability_mixture]
  apply FiniteDistribution.expectation_congr
  intro base
  rw [fixedPair_eq]
  rw [HierarchicalUsefulCollision.pairLaw, FiniteDistribution.probability_pushforward,
    HierarchicalUsefulCollision.law, CompletionSoundness.sigmaLaw_probability]
  rfl

end
end PerfectCompleteness.StoppedProjectedPairMean

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalUsefulBackground
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalUsefulBackground

open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalUsefulBackground.backgroundFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalUsefulBackground.rowSpaceFintype
variable {P : Type*} [Fintype P]
  (externalLaw : FiniteDistribution P)
  (background : P → HierarchicalAgreementMean.Background (rows := rows) slots upper)
  (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
  (hrows : 0 < rows (Nodes.height upper))

theorem pairLaw_background :
    (HierarchicalUsefulCollision.pairLaw slots upper externalLaw background scalarLaw hrows).pushforward
        Prod.fst = externalLaw.pushforward background := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, HierarchicalUsefulCollision.pairLaw,
    FiniteDistribution.probability_pushforward, FiniteDistribution.probability_pushforward]
  change (CompletionSoundness.sigmaLaw externalLaw
      (fun p => HierarchicalUsefulCollision.bucketLaw slots upper (scalarLaw p) hrows)).probability
        (fun sample => event (background sample.1)) =
      externalLaw.probability (fun p => event (background p))
  exact CompletionSoundness.sigmaLaw_probability_first externalLaw
    (fun p => HierarchicalUsefulCollision.bucketLaw slots upper (scalarLaw p) hrows)
    (fun p => event (background p))

end
end PerfectCompleteness.HierarchicalUsefulBackground

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedSourcePairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedSourcePairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}

private theorem mixture_product {A B X : Type*} [Fintype A] [Fintype B] [Fintype X]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (P : A × B → FiniteDistribution X) :
    (μ.product ν).mixture P = μ.mixture (fun a => ν.mixture (fun b => P (a, b))) := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  simp only [FiniteDistribution.probability_mixture]
  exact FiniteDistribution.expectation_product μ ν
    (fun z : A × B => (P z).probability event)

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

attribute [local instance] OAI.PerfectCompleteness.StoppedSourcePairLaw.backgroundFintype
local instance rowSpaceFintype_r767f39_2 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
local instance nativeBackgroundFintype_r767f39_1 :
    Fintype (HierarchicalAgreementMean.Background (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _
local instance nativeRowSpaceFintype_r767f39_2 :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _
theorem pairedLaw_eq_modified (hbranch : ∀ k < j + 1, 0 < branch k)
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) :
    HierarchicalAdviceFromBuckets.pairedLaw
      (StoppedProjectedBuckets.experiment clauses rows repeats hupper hij designated hrows o hbranch
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ') σ)
      (StoppedProjectedBuckets.externalLaw clauses rows repeats hupper hij designated hrows o hbranch
        (fun _ => ProjectionPosterior.bernoulli β hβ hβ'))
      (StoppedProjectedBuckets.background clauses rows repeats hupper hij designated hrows o)
      (StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated hrows o)
      (StoppedProjectedBuckets.rows_positive rows hupper hrows o) =
      UpperCutTriangle.modifiedPairLaw rows repeats (StoppedProjectedExperiment.upperPath hupper o)
        (Nat.succ_le_succ hij.le) (StoppedProjectedExperiment.nativeSlots clauses o)
        hbranch (hrows j) (SourceProjectedWholeChoices.projected clauses hupper hij o)
        (SourceProjectedWholeChoices.projection clauses hupper hij o)
        (fun _ => SourceProjectedChoices.choiceLaw (t := t)) β hβ hβ' := by
  rw [StoppedProjectedPairMean.pairedLaw_eq_mixture]
  unfold StoppedProjectedBucketIndex.baseLaw UpperCutTriangle.modifiedPairLaw
  rw [mixture_product]
  apply congrArg ((GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le) hbranch).mixture)
  funext lowerPref
  exact (prefix_pair_law clauses rows repeats hupper hij designated hrows o lowerPref β hβ hβ').symm

end
end PerfectCompleteness.StoppedSourcePairLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FixedSourcePairVariation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourcePairVariation

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype
attribute [local instance 2000] HierarchicalUsefulCollision.backgroundFintype
  HierarchicalUsefulCollision.rowSpaceFintype

private theorem sigma_variation_le_const
    {O : Type*} [Fintype O] {R : O → Type*} [∀ o, Fintype (R o)]
    (outer : FiniteDistribution O)
    (P Q : (o : O) → FiniteDistribution (R o))
    (error : ℝ) (bound : ∀ o, (P o).totalVariation (Q o) ≤ error) :
    (CompletionSoundness.sigmaLaw outer P).totalVariation
      (CompletionSoundness.sigmaLaw outer Q) ≤ error := by
  rw [ConditionalVariation.sigma_totalVariation outer P Q]
  calc
    outer.expectation (fun o => (P o).totalVariation (Q o)) ≤
        outer.expectation (fun _ => error) :=
      SmallBias.expectation_mono outer bound
    _ = error := SmallBias.expectation_const outer error

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  {n i j v m : Nat}

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (FixedParameters.branch parameters i) → Slots (FixedParameters.branch parameters) i)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (FixedParameters.branch parameters) n
  (FixedRows.sourceLength parameters.plan hδ)))

local instance backgroundFintype_r767f39_1 (o : Outer (n := n) (j := j) (m := m) parameters) :
    Fintype (HierarchicalAgreementMean.Background (rows := FixedRows.rows parameters.plan)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _
local instance rowSpaceFintype_r767f39_3 (o : Outer (n := n) (j := j) (m := m) parameters) :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _
theorem fiber_lt_six (hroot : n ≤ parameters.plan.depth)
    (o : Outer (n := n) (j := j) (m := m) parameters) :
    (HierarchicalAdviceFromBuckets.pairedLaw (experiment parameters clauses hupper hij designated σ o)
      (externalLaw parameters clauses hupper hij designated o)
      (background parameters clauses hupper hij designated o)
      (scalarLaw parameters clauses hupper hij designated o) (upperRows parameters hupper o)).totalVariation
      (HierarchicalAgreementMean.referenceLaw
        (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
        ((externalLaw parameters clauses hupper hij designated o).pushforward
          (background parameters clauses hupper hij designated o)) (upperRows parameters hupper o)) <
      6 * parameters.accuracy := by
  let pref := StoppedProjectedExperiment.upperPath hupper o
  let slots := StoppedProjectedExperiment.nativeSlots clauses o
  let projected := SourceProjectedWholeChoices.projected clauses hupper hij o
  let projection := SourceProjectedWholeChoices.projection clauses hupper hij o
  let choiceLaw := fun _ : UpperCutTriangle.Prefix (FixedParameters.branch parameters) j i =>
    SourceProjectedChoices.choiceLaw
      (branch := FixedParameters.branch parameters) (n := i)
      (t := FixedRows.sourceLength parameters.plan hδ)
  have hpair := StoppedSourcePairLaw.pairedLaw_eq_modified clauses
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan) hupper hij designated
    (positiveRows parameters) o (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedParameters.projectionProbability parameters i : ℝ)
    (by exact_mod_cast (FixedParameters.projectionProbability_bounds parameters i).1.le)
    (by exact_mod_cast (FixedParameters.projectionProbability_bounds parameters i).2.le) σ
  change HierarchicalAdviceFromBuckets.pairedLaw
      (experiment parameters clauses hupper hij designated σ o)
      (externalLaw parameters clauses hupper hij designated o)
      (background parameters clauses hupper hij designated o)
      (scalarLaw parameters clauses hupper hij designated o) (upperRows parameters hupper o) =
    FixedUpperCutTriangle.modifiedPairLaw parameters pref (Nat.succ_le_succ hij.le) slots
      projected projection choiceLaw at hpair
  have h := FixedUpperCutTriangle.original_reference_lt parameters pref
    (Nat.succ_le_succ hij.le) slots projected projection choiceLaw hroot
  change (FixedUpperCutTriangle.modifiedPairLaw parameters pref (Nat.succ_le_succ hij.le) slots
      projected projection choiceLaw).totalVariation
    (HierarchicalAgreementMean.referenceLaw slots (upperNode pref)
      ((FixedUpperCutTriangle.modifiedPairLaw parameters pref (Nat.succ_le_succ hij.le) slots
        projected projection choiceLaw).pushforward Prod.fst) (upperRows parameters hupper o)) <
      6 * parameters.accuracy at h
  rw [← hpair] at h
  have hbackground :
      (HierarchicalAdviceFromBuckets.pairedLaw
        (experiment parameters clauses hupper hij designated σ o)
        (externalLaw parameters clauses hupper hij designated o)
        (background parameters clauses hupper hij designated o)
        (scalarLaw parameters clauses hupper hij designated o)
        (upperRows parameters hupper o)).pushforward Prod.fst =
      (externalLaw parameters clauses hupper hij designated o).pushforward
        (background parameters clauses hupper hij designated o) :=
    HierarchicalUsefulBackground.pairLaw_background slots (upperNode pref)
      (externalLaw parameters clauses hupper hij designated o)
      (background parameters clauses hupper hij designated o)
      (scalarLaw parameters clauses hupper hij designated o) (upperRows parameters hupper o)
  have hvariation := congrArg
    (fun backgroundLaw : FiniteDistribution
        (HierarchicalAgreementMean.Background (rows := FixedRows.rows parameters.plan)
          slots (upperNode pref)) =>
      (HierarchicalUsefulCollision.pairLaw slots (upperNode pref)
        (externalLaw parameters clauses hupper hij designated o)
        (background parameters clauses hupper hij designated o)
        (scalarLaw parameters clauses hupper hij designated o)
        (upperRows parameters hupper o)).totalVariation
        (HierarchicalAgreementMean.referenceLaw slots (upperNode pref)
          backgroundLaw (upperRows parameters hupper o))) hbackground
  exact lt_of_eq_of_lt hvariation.symm h

theorem totalVariation_le_six (hroot : n ≤ parameters.plan.depth)
    (outer : FiniteDistribution (Outer (n := n) (j := j) (m := m) parameters)) :
    (actualLaw parameters clauses hupper hij designated σ outer).totalVariation
      (referenceLaw parameters clauses hupper hij designated σ outer) ≤ 6 * parameters.accuracy := by
  exact sigma_variation_le_const
    (R := PairFiber parameters clauses hupper) outer
    (fun o => HierarchicalAdviceFromBuckets.pairedLaw
      (experiment parameters clauses hupper hij designated σ o)
      (externalLaw parameters clauses hupper hij designated o)
      (background parameters clauses hupper hij designated o)
      (scalarLaw parameters clauses hupper hij designated o) (upperRows parameters hupper o))
    (fun o => HierarchicalAgreementMean.referenceLaw
      (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
      ((externalLaw parameters clauses hupper hij designated o).pushforward
        (background parameters clauses hupper hij designated o)) (upperRows parameters hupper o))
    (6 * parameters.accuracy)
    (fun o => (fiber_lt_six parameters clauses hupper hij designated σ hroot o).le)

theorem totalVariation_le_ten (hroot : n ≤ parameters.plan.depth)
    (outer : FiniteDistribution (Outer (n := n) (j := j) (m := m) parameters)) :
    (actualLaw parameters clauses hupper hij designated σ outer).totalVariation
      (referenceLaw parameters clauses hupper hij designated σ outer) ≤ 10 * parameters.accuracy := by
  have h := totalVariation_le_six parameters clauses hupper hij designated σ hroot outer
  have hpositive := parameters.accuracy_pos
  linarith

end
end PerfectCompleteness.FixedSourcePairVariation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedStoppedUpperProbability
attribute [-instance] _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedUpperProbability

noncomputable section

attribute [local instance] FixedStoppedDecoderLaw.sampleFintype
  UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (strategy : FixedPreliminaryGame.Strategy parameters input)

theorem pairedVariation_le_oai :
    FixedStoppedInverseBound.pairedVariation parameters i j hij input strategy ≤
      10 * parameters.accuracy :=
  FixedSourcePairVariation.totalVariation_le_ten parameters
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
    (Nat.succ_le_of_lt j.isLt) hij (FixedStoppedPhysicalLaw.designated parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy) (le_refl _)
    (FixedStoppedInverseBound.outerLaw parameters j input)

end
end PerfectCompleteness.FixedStoppedUpperProbability

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedUpperProbability.pairedVariation_le_oai := @OAI.PerfectCompleteness.FixedStoppedUpperProbability.pairedVariation_le_oai
