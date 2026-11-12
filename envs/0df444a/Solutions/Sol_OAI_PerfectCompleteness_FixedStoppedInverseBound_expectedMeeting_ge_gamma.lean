-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedInverseBound.expectedMeeting_ge_gamma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:23:23.708227+00:00
-- url     : https://prove2.me/submissions/5081c2b5-e865-4994-931d-826c5cb41ecf

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
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalAdviceFamily_prediction_difference
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalBucketFamily_mean_agreement_ge
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalProjectedPrediction_J_probability
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalProjectedRawAverage_expectedMeeting_ge_prediction_difference
import Theorems.Thm_OAI_PerfectCompleteness_WholeArrayInteriorOwnInputLaw_exposedRead_law

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

theorem expectation_comm (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → Γ → ℝ) :
    μ.expectation (fun x => ν.expectation (f x)) =
      ν.expectation (fun y => μ.expectation (fun x => f x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact mul_left_comm _ _ _

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DualQuotientRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.SmallBiasSlice

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem expectation_const_mul (μ : FiniteDistribution Ω) (c : ℝ) (g : Ω → ℝ) :
    μ.expectation (fun x => c * g x) = c * μ.expectation g := by
  unfold FiniteDistribution.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring


end

end PerfectCompleteness.SmallBiasSlice

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_DensityVariation
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

theorem expectation_sub (μ : FiniteDistribution Ω) (f g : Ω → ℝ) :
    μ.expectation (fun x => f x - g x) = μ.expectation f - μ.expectation g := by
  simp only [FiniteDistribution.expectation, mul_sub, Finset.sum_sub_distrib]

end
end PerfectCompleteness.DensityVariation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.OwnInputCanonicalQuery

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

theorem assemble_original (arrays : Arrays slots rows) :
    assemble slots rows upper lower (arrays upper) (exteriorOf slots rows upper lower arrays) = arrays := by
  funext node
  by_cases hu : node = upper
  · subst node
    exact assemble_upper slots rows upper lower _ _
  · by_cases hl : node = lower
    · subst node
      simp only [assemble, dite_eq_right hu, dite_eq_left rfl, exteriorOf]
    · simp only [assemble, dite_eq_right hu, dite_eq_right hl, exteriorOf]

end
end PerfectCompleteness.OwnInputCanonicalQuery

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CandidateCoupling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

theorem probability_eq_expectation {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (event : X → Bool) :
    μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    mul_ite, mul_one, mul_zero]

end
end PerfectCompleteness.CandidateCoupling

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedExperimentLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedExperiment

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows repeats : Nat → Nat} {n t : Nat} {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (lower : K → Nodes branch n)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block rows (lower k))

theorem rawRead_expectation (outer : FiniteDistribution K) (r : Nat)
    (f : RawSample (rows := rows) (repeats := repeats) projected upper lower cut r → ℝ) :
    ((originalLaw projected upper lower cut outer).product
      (FiniteDistribution.uniform (Advice (rows := rows) upper r))).expectation
        (fun x => f (rawRead projected upper lower cut r x)) =
      (rawLaw projected upper lower cut outer r).expectation f := by
  rw [FiniteDistribution.expectation_product]
  rw [FiniteDistribution.expectation_comm]
  unfold rawLaw
  rw [CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro A
  unfold originalLaw
  rw [CandidateCoupling.expectation_sigmaLaw, CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro k
  have h := WholeArrayInteriorOwnInputLaw.exposedRead_law rows repeats (projected k) upper
    (lower k) (cut k) (LinearMap.ker A)
  rw [← h, FiniteDistribution.expectation_pushforward]
  rfl

theorem rawRead_law (outer : FiniteDistribution K) (r : Nat) :
    ((originalLaw (rows := rows) (repeats := repeats) projected upper lower cut outer).product
      (FiniteDistribution.uniform (Advice (rows := rows) upper r))).pushforward
        (rawRead projected upper lower cut r) =
      rawLaw projected upper lower cut outer r := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward,
    CandidateCoupling.probability_eq_expectation,
    CandidateCoupling.probability_eq_expectation]
  exact rawRead_expectation projected upper lower cut outer r
    (fun x => if event x then 1 else 0)

theorem experiment_rawRead_law (outer : FiniteDistribution K)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (r : Nat) :
    (HierarchicalAdviceExperiment.originalLaw
      (experiment (repeats := repeats) slots projected projection upper lowerLevel lower cut
        direction outer σ) r).pushforward (rawRead projected upper lower cut r) =
      rawLaw projected upper lower cut outer r :=
  rawRead_law projected upper lower cut outer r

end
end PerfectCompleteness.HierarchicalProjectedExperiment


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedComparisonErrorsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalFixedAdvice

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {branch : Nat → Nat} {t : Nat} {Ω P : Type*} [Fintype Ω] [Fintype P]
  (S : HierarchicalAdviceExperiment.Experiment branch (FixedRows.rows p.plan) p.plan.depth t Ω)

local instance backgroundFintype_r8bab77_1 : Fintype (HierarchicalAdviceExperiment.Background S) :=
  Fintype.ofFinite _
local instance rowSpaceFintype_r8bab77_1 : Fintype (NodeEmbedding.RowSpace S.slots S.upper) :=
  Fintype.ofFinite _
local instance inputFintype_r8bab77_1 :
    (b : HierarchicalAdviceExperiment.Background S) → Fintype (HierarchicalAdviceExperiment.Input S b) :=
  HierarchicalAdviceExperiment.inputFintype S
theorem paired_error_small : 10 * p.accuracy ≤ simultaneous δ ^ 2 / 16 := by
  have hs := p.accuracy_small 0 (Nat.zero_le _)
  simp only [CommonAccuracy.tolerance, lt_min_iff] at hs
  linarith [hs.2.1]

end
end PerfectCompleteness.HierarchicalFixedAdvice


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeArrayRawAssembly
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeArrayRawAssembly

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open WholeArrayInteriorOwnInputLaw (fullPath exposedRead exteriorLaw)

variable {branch : Nat → Nat} {N h k t : Nat}

private theorem mergedBuckets_step (rows repeats : Nat → Nat)
    (j : Fin (branch N)) (p : Path branch N h) (q : Path branch h k)
    (hproper : k < h)
    (slots : Slots branch (N + 1) → Fin t → MixedSupport.Slot)
    (W : Submodule F2 (Fin (rows h) → F2))
    (ω : WholeArraySampler.Tape rows repeats ((Path.step j p).append q) slots) :
    mergedBuckets rows repeats (.step j p) q hproper slots W ω =
      mergedBuckets rows repeats p q hproper (childSlots slots j)
        W (ω (.inr (.inl ()))) := by
  cases q with
  | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
  | step i q => rfl

private theorem upper_rows_split (rows repeats : Nat → Nat) :
    ∀ {N k : Nat} (upper : Nodes branch N)
      (q : Path branch (Nodes.height upper) k) (hproper : k < Nodes.height upper)
      (slots : Slots branch N → Fin t → MixedSupport.Slot)
      (W : Submodule F2 (Block rows upper))
      (ω : WholeArraySampler.Tape rows repeats ((Nodes.path upper).append q) slots),
      BucketSampler.evaluate (rows (Nodes.height upper))
          (RecursiveSampler.evaluate F2 repeats q (LeafDomain (nodeSlots slots upper)))
          (mergedBuckets rows repeats (Nodes.path upper) q hproper slots W ω) =
        WholeArraySampler.evaluate rows repeats ((Nodes.path upper).append q) slots ω upper := by
  intro N
  induction N with
  | zero => intro k upper; exact nomatch upper
  | succ N ih =>
      intro k upper q hproper slots W ω
      cases upper with
      | inl u =>
          cases u
          cases q with
          | refl => exact False.elim ((Nat.lt_irrefl _) hproper)
          | step i q =>
              change BucketSampler.evaluate (rows (N + 1))
                (RecursiveSampler.evaluate F2 repeats (.step i q) (LeafDomain slots))
                ((HiddenBucketBias.splitTape W _).symm
                  (HiddenBucketBias.splitTape W _ (ω (.inl ())))) =
                BucketSampler.evaluate (rows (N + 1))
                  (RecursiveSampler.evaluate F2 repeats (.step i q) (LeafDomain slots))
                  (ω (.inl ()))
              exact congrArg
                (BucketSampler.evaluate (rows (N + 1))
                  (RecursiveSampler.evaluate F2 repeats (.step i q) (LeafDomain slots)))
                ((HiddenBucketBias.splitTape W _).symm_apply_apply (ω (.inl ())))
      | inr pair =>
          rcases pair with ⟨j, upper⟩
          change BucketSampler.evaluate (rows (Nodes.height upper))
            (RecursiveSampler.evaluate F2 repeats q
              (LeafDomain (nodeSlots (childSlots slots j) upper)))
            (mergedBuckets rows repeats (.step j (Nodes.path upper)) q hproper slots W ω) =
            WholeArraySampler.evaluate rows repeats (.step j ((Nodes.path upper).append q))
              slots ω (.inr (j, upper))
          exact (congrArg
            (BucketSampler.evaluate (rows (Nodes.height upper))
              (RecursiveSampler.evaluate F2 repeats q
                (LeafDomain (nodeSlots (childSlots slots j) upper))))
            (mergedBuckets_step rows repeats j (Nodes.path upper) q hproper slots W ω)).trans
              ((ih upper q hproper (childSlots slots j) W (ω (.inr (.inl ())))).trans
                (WholeArraySampler.evaluate_selected rows repeats j
                  ((Nodes.path upper).append q) slots ω upper).symm)

variable (rows repeats : Nat → Nat)
  (slots : Slots branch N → Fin t → MixedSupport.Slot)
  (upper lower : Nodes branch N) (cut : OwnInputReference.Cut upper lower)
  (W : Submodule F2 (Block rows upper))

theorem arrays_exposedRead
    (ω : WholeArraySampler.Tape rows repeats (fullPath upper lower cut) slots) :
    OwnInputRawAssembly.arrays slots rows upper lower W repeats cut
        (exposedRead rows repeats slots upper lower cut W ω) =
      WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω := by
  have hupper := upper_rows_split rows repeats upper cut.path cut.proper slots W ω
  change OwnInputCanonicalQuery.assemble slots rows upper lower
    (BucketSampler.evaluate (rows (Nodes.height upper))
      (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
      (mergedBuckets rows repeats (Nodes.path upper) cut.path cut.proper slots W ω))
    (OwnInputCanonicalQuery.exteriorOf slots rows upper lower
      (WholeArraySampler.evaluate rows repeats (fullPath upper lower cut) slots ω)) = _
  rw [hupper]
  exact OwnInputCanonicalQuery.assemble_original slots rows upper lower _

end
end PerfectCompleteness.WholeArrayRawAssembly

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedPredictionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedPrediction

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows repeats : Nat → Nat} {n t : Nat} {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (lower : K → Nodes branch n)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block rows (lower k))
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (κ : ℝ) (r : Nat) (ρ : ℝ)

local notation "S" => HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
  slots projected projection upper lowerLevel lower cut direction outer σ


theorem prediction_rawRead
    (x : HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      projected upper lower cut × HierarchicalProjectedExperiment.Advice (rows := rows) upper r) :
    HierarchicalAdviceExperiment.prediction S κ r ρ x =
      rawPrediction (repeats := repeats)
        slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ
        (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
          projected upper lower cut r x) := by
  rcases x with ⟨⟨k, ω⟩, A⟩
  exact (congrArg
    (fun X : Arrays slots rows =>
      HierarchicalPrediction.prediction slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper X) σ (lower k)
        (cut k).upper_ne_lower (direction k) (S).original (S).arrays
        (HierarchicalAdviceExperiment.lowerEvent S) κ r ρ A (NodeEmbedding.matrix X upper))
    (congrArg (ChildBlockProjection.arraysPullback rows (projection k))
      (WholeArrayRawAssembly.arrays_exposedRead rows repeats (projected k) upper (lower k) (cut k)
        (LinearMap.ker A) ω))).symm

theorem prediction_probability :
    (HierarchicalAdviceExperiment.originalLaw S r).probability
        (HierarchicalAdviceExperiment.prediction S κ r ρ) =
      (HierarchicalProjectedExperiment.rawLaw (rows := rows) (repeats := repeats)
        projected upper lower cut outer r).probability
        (rawPrediction (repeats := repeats)
          slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ) := by
  have h := congrArg
    (fun μ : FiniteDistribution
        (HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
          projected upper lower cut r) =>
      μ.probability (rawPrediction (repeats := repeats)
        slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ))
    (HierarchicalProjectedExperiment.experiment_rawRead_law (rows := rows) (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ r)
  have hp := FiniteDistribution.probability_pushforward
    (Ω := HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
      projected upper lower cut × HierarchicalProjectedExperiment.Advice (rows := rows) upper r)
    (Γ := HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
      projected upper lower cut r)
    (HierarchicalAdviceExperiment.originalLaw S r)
    (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
      projected upper lower cut r)
    (rawPrediction (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ)
  have hp' := hp.symm.trans h
  have hevent : (fun x => rawPrediction (repeats := repeats)
      slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ
      (HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
        projected upper lower cut r x)) =
      HierarchicalAdviceExperiment.prediction S κ r ρ :=
    funext (fun x =>
      (prediction_rawRead (repeats := repeats)
        slots projected projection upper lowerLevel lower cut direction outer σ κ r ρ x).symm)
  exact (congrArg (fun event =>
    (HierarchicalAdviceExperiment.originalLaw S r).probability event) hevent).symm.trans hp'

end
end PerfectCompleteness.HierarchicalProjectedPrediction



namespace PerfectCompleteness.HierarchicalProjectedAverage

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Projected

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  {K : Type*} [Fintype K]
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projected : K → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ k s j, MixedSupport.Projection (slots s j) (projected k s j))
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (lower : K → Nodes branch plan.depth)
  (cut : ∀ k, OwnInputReference.Cut upper (lower k))
  (direction : ∀ k, Block (FixedRows.rows plan) (lower k))
  (outer : FiniteDistribution K)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

local notation "S" => HierarchicalProjectedExperiment.experiment
  (rows := FixedRows.rows plan) (repeats := FixedRows.repeats plan)
  slots projected projection upper lowerLevel lower cut direction outer σ

theorem expectedMeeting_eq_fibers :
    expectedMeeting plan slots projected projection upper lowerLevel lower cut direction outer σ =
      (FiniteDistribution.uniform
        (HierarchicalProjectedExperiment.Advice (rows := FixedRows.rows plan) upper plan.order)).expectation
        (fun A => outer.expectation (fun k =>
          HierarchicalProjectedRawAverage.expectedMeeting plan slots (projected k) (projection k) upper (lower k) lowerLevel
            (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k)
            (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
              (projected k) upper (lower k) (cut k)))) := by
  simp only [expectedMeeting, HierarchicalProjectedExperiment.rawLaw,
    CandidateCoupling.expectation_sigmaLaw]
  rfl

theorem predictionDifference_eq_fibers :
    predictionDifference plan slots projected projection upper lowerLevel lower cut direction outer σ =
      (FiniteDistribution.uniform
        (HierarchicalProjectedExperiment.Advice (rows := FixedRows.rows plan) upper plan.order)).expectation
        (fun A => outer.expectation (fun k =>
          (HierarchicalProjectedRawAverage.law plan (projected k) upper (lower k) A (cut k)
            (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
              (projected k) upper (lower k) (cut k))).probability
            (HierarchicalProjectedRawAverage.prediction plan slots (projected k) (projection k) upper (lower k) lowerLevel
              (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k)) -
          rhoPred (useful δ) plan.density *
            (HierarchicalProjectedRawAverage.law plan (projected k) upper (lower k) A (cut k)
              (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
                (projected k) upper (lower k) (cut k))).probability
              (HierarchicalProjectedRawAverage.J plan slots (projected k) (projection k) upper (lower k) lowerLevel
                (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (cut k)))) := by
  unfold predictionDifference
  rw [HierarchicalProjectedPrediction.prediction_probability slots projected projection upper lowerLevel lower cut direction outer σ
      (useful δ) plan.order plan.density,
    HierarchicalProjectedPrediction.J_probability slots projected projection upper lowerLevel lower cut direction outer σ
      (useful δ) plan.order plan.density]
  simp only [HierarchicalProjectedExperiment.rawLaw, CompletionSoundness.sigmaLaw_probability,
    DensityVariation.expectation_sub, SmallBiasSlice.expectation_const_mul]
  rfl

theorem expectedMeeting_ge_prediction_difference (hδ : 0 < δ) :
    HierarchicalProjectedRawAverage.factor plan upper *
      predictionDifference plan slots projected projection upper lowerLevel lower cut direction outer σ ≤
      expectedMeeting plan slots projected projection upper lowerLevel lower cut direction outer σ := by
  rw [predictionDifference_eq_fibers, expectedMeeting_eq_fibers,
    ← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro A
  rw [← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro k
  exact HierarchicalProjectedRawAverage.expectedMeeting_ge_prediction_difference plan slots (projected k)
    (projection k) upper (lower k) lowerLevel
    (S).original (S).arrays (HierarchicalAdviceExperiment.lowerEvent S) σ A (direction k) (cut k) hδ
    (WholeArrayInteriorOwnInputLaw.exteriorLaw (FixedRows.rows plan) (FixedRows.repeats plan)
      (projected k) upper (lower k) (cut k))

end Projected


end
end PerfectCompleteness.HierarchicalProjectedAverage



namespace PerfectCompleteness.HierarchicalProjectedOuterAverage

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ)

theorem factor_nonneg (ℓ : Nat) : 0 ≤ factor plan ℓ := by
  unfold factor
  positivity

theorem factor_mul_b_eq_gamma (ℓ : Nat) :
    factor plan ℓ * b (useful δ) plan.density (inverse δ) plan.order ℓ =
      gamma (useful δ) plan.density (inverse δ) plan.order ℓ := by
  unfold factor gamma
  rw [pow_add]
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

variable {branch : Nat → Nat} {t : Nat} {O : Type*} [Fintype O]
  {K : O → Type*} [∀ o, Fintype (K o)]
  (slots : O → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projected : (o : O) → K o → RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ o k s j, MixedSupport.Projection (slots o s j) (projected o k s j))
  (upper : O → Nodes branch plan.depth) (lowerLevel : Nat)
  (lower : (o : O) → K o → Nodes branch plan.depth)
  (cut : ∀ o k, OwnInputReference.Cut (upper o) (lower o k))
  (direction : ∀ o k, Block (FixedRows.rows plan) (lower o k))
  (inner : (o : O) → FiniteDistribution (K o))
  (outer : FiniteDistribution O)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

local notation "S" => experiment plan slots projected projection upper lowerLevel lower cut direction inner σ

theorem predictionDifference_eq_mean :
    predictionDifference plan slots projected projection upper lowerLevel lower cut direction inner outer σ =
      outer.expectation (fun o => HierarchicalProjectedAverage.predictionDifference plan
        (slots o) (projected o) (projection o) (upper o) lowerLevel (lower o) (cut o)
        (direction o) (inner o) σ) := by
  simp only [predictionDifference, HierarchicalProjectedAverage.predictionDifference,
    HierarchicalAdviceFamily.originalLaw,
    HierarchicalAdviceFamily.prediction, HierarchicalAdviceFamily.J, HierarchicalAdviceFamily.observe,
    CompletionSoundness.sigmaLaw_probability, DensityVariation.expectation_sub,
    SmallBiasSlice.expectation_const_mul]
  rfl

theorem expectedMeeting_ge_prediction_difference (hδ : 0 < δ)
    (ℓ : Nat) (hrowdim : ∀ o, FixedRows.rows plan (Nodes.height (upper o)) = ℓ) :
    factor plan ℓ *
      predictionDifference plan slots projected projection upper lowerLevel lower cut direction inner outer σ ≤
      expectedMeeting plan slots projected projection upper lowerLevel lower cut direction inner outer σ := by
  unfold expectedMeeting
  rw [predictionDifference_eq_mean, ← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro o
  have h := HierarchicalProjectedAverage.expectedMeeting_ge_prediction_difference plan
    (slots o) (projected o) (projection o) (upper o) lowerLevel (lower o) (cut o)
    (direction o) (inner o) σ hδ
  have hfactor : HierarchicalProjectedRawAverage.factor plan (upper o) = factor plan ℓ := by
    simp only [HierarchicalProjectedRawAverage.factor, factor, hrowdim o]
  rw [hfactor] at h
  exact h

end
end PerfectCompleteness.HierarchicalProjectedOuterAverage



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_HierarchicalFixedAdviceFamilyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalFixedAdviceFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

theorem inverse_factor_eq_q (level : Nat) :
    ((inverse δ) ^ 2 / 4) /
        ((2 : ℝ) ^ (p.plan.order * FixedRows.rows p.plan level)) ^ 2 =
      q (inverse δ) p.plan.order (FixedRows.rows p.plan level) := by
  simp only [q, g, h, div_eq_mul_inv, pow_two]
  ring

theorem coarse_error_small (level : Nat) (hlevel : level ≤ p.plan.depth) :
    10 * p.accuracy ≤ p.plan.density *
      (((inverse δ) ^ 2 / 4) /
        ((2 : ℝ) ^ (p.plan.order * FixedRows.rows p.plan level)) ^ 2) / 16 := by
  rw [inverse_factor_eq_q p level]
  have hs := p.accuracy_small level hlevel
  simp only [CommonAccuracy.tolerance, lt_min_iff] at hs
  linarith [hs.2.2.1]

variable {branch : Nat → Nat} {t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment
    branch (FixedRows.rows p.plan) p.plan.depth t (Ω o))

attribute [local instance] OAI.PerfectCompleteness.HierarchicalFixedAdviceFamily.backgroundFiberFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalFixedAdviceFamily.rowSpaceFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalFixedAdviceFamily.inputFintype
local instance valueFintype_r8bab77_1 (z : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Value S z) :=
  HierarchicalAdviceFamily.valueFintype S z
attribute [local instance] OAI.PerfectCompleteness.HierarchicalFixedAdviceFamily.coarseFintype
variable {P : O → Type*} [∀ o, Fintype (P o)]
  (outer : FiniteDistribution O)
  (externalLaw : (o : O) → FiniteDistribution (P o))
  (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
  (scalarLaw : (o : O) → P o →
    FiniteDistribution (NodeEmbedding.RowSpace (S o).slots (S o).upper))
  (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))

theorem mean_agreement_ge
    (hmass : simultaneous δ / 2 ≤ HierarchicalBucketFamily.usefulMass S (useful δ)
      outer externalLaw background scalarLaw (rows_positive p S))
    (hpaired : (HierarchicalBucketFamily.actualPairLaw S outer externalLaw background
      scalarLaw (rows_positive p S)).totalVariation
        (HierarchicalBucketFamily.referencePairLaw S outer backgrounds (rows_positive p S)) ≤
        10 * p.accuracy) :
    2 * inverse δ ≤ (HierarchicalAdviceFamily.backgroundLaw S outer backgrounds).expectation
      (fun z => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceFamily.table S (useful δ) z)) := by
  calc
    2 * inverse δ = simultaneous δ ^ 2 / 16 := by unfold inverse; ring
    _ ≤ _ := HierarchicalBucketFamily.mean_agreement_ge S (useful δ) outer externalLaw
      background scalarLaw (rows_positive p S) backgrounds (simultaneous δ)
      (simultaneous_pos hδ).le hmass (hpaired.trans (HierarchicalFixedAdvice.paired_error_small p))

theorem prediction_difference (level : Nat) (hlevel : level ≤ p.plan.depth)
    (hheight : ∀ o, Nodes.height (S o).upper = level)
    (hmass : simultaneous δ / 2 ≤ HierarchicalBucketFamily.usefulMass S (useful δ)
      outer externalLaw background scalarLaw (rows_positive p S))
    (hpaired : (HierarchicalBucketFamily.actualPairLaw S outer externalLaw background
      scalarLaw (rows_positive p S)).totalVariation
        (HierarchicalBucketFamily.referencePairLaw S outer backgrounds (rows_positive p S)) ≤
        10 * p.accuracy)
    (hcoarse : ((HierarchicalAdviceFamily.originalLaw S outer p.plan.order).pushforward
      (HierarchicalAdviceFamily.observe S p.plan.order)).totalVariation
        ((HierarchicalAdviceFamily.referenceLaw S outer backgrounds p.plan.order).pushforward
          (HierarchicalAdviceFamily.referenceObserve S p.plan.order)) ≤ 10 * p.accuracy) :
    b (useful δ) p.plan.density (inverse δ) p.plan.order (FixedRows.rows p.plan level) ≤
      predictionDifference p S outer := by
  have hdim (o : O) :
      FixedRows.rows p.plan (Nodes.height (S o).upper) ≤ FixedRows.rows p.plan level := by
    rw [hheight o]
  have hbound := HierarchicalAdviceFamily.prediction_difference S (useful δ)
    (useful_pos hδ).le outer backgrounds (rows_positive p S)
    (FixedRows.rows p.plan level) hdim p.plan.order p.plan.density (inverse δ)
    (10 * p.accuracy) (inverse_pos hδ) p.plan.density_pos p.plan.density_lt p.plan.spectral
    (mean_agreement_ge p S outer externalLaw background scalarLaw backgrounds hmass hpaired)
    (by have := p.accuracy_pos; positivity) (coarse_error_small p level hlevel) hcoarse
  rw [inverse_factor_eq_q p level] at hbound
  have hfactor : useful δ * p.plan.density *
      q (inverse δ) p.plan.order (FixedRows.rows p.plan level) / 4 =
      b (useful δ) p.plan.density (inverse δ) p.plan.order (FixedRows.rows p.plan level) := by
    unfold b rhoPred
    ring
  rw [hfactor] at hbound
  exact hbound

end
end PerfectCompleteness.HierarchicalFixedAdviceFamily


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedInverseBound
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedInverseBound

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

local notation "S" => experiment parameters i j hij input strategy

attribute [local instance] OAI.PerfectCompleteness.FixedStoppedInverseBound.nativeBackgroundFintype
local instance nativeRowSpaceFintype_r8bab77_1 (o : Outer parameters j input) :
    Fintype (NodeEmbedding.RowSpace
      (StoppedProjectedExperiment.nativeSlots (clauses input) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)) :=
  HierarchicalUsefulCollision.rowSpaceFintype
    (StoppedProjectedExperiment.nativeSlots (clauses input) o)
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
attribute [local instance] OAI.PerfectCompleteness.FixedStoppedInverseBound.pairFiberFintype
attribute [local instance] OAI.PerfectCompleteness.FixedStoppedInverseBound.pairSampleFintype
local instance backgroundFintype_r8bab77_2 (o : Outer parameters j input) :
    Fintype (HierarchicalAdviceExperiment.Background (S o)) :=
  HierarchicalAdviceExperiment.backgroundFintype (S o)
attribute [local instance] OAI.PerfectCompleteness.FixedStoppedInverseBound.coarseFintype
local instance inputFintype_r8bab77_2 (o : Outer parameters j input)
    (bg : HierarchicalAdviceExperiment.Background (S o)) :
    Fintype (HierarchicalAdviceExperiment.Input (S o) bg) :=
  HierarchicalAdviceExperiment.inputFintype (S o) bg
attribute [local instance] OAI.PerfectCompleteness.FixedStoppedInverseBound.projectedSampleFintype
attribute [local instance] OAI.PerfectCompleteness.FixedStoppedInverseBound.adviceFintype
local instance originalFiberFintype_r8bab77_1 (o : Outer parameters j input) (r : Nat) :
    Fintype (HierarchicalProjectedExperiment.Sample
      (rows := FixedRows.rows parameters.plan) (repeats := FixedRows.repeats parameters.plan)
      (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) o)
      (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o)
      (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o)
      (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij o) ×
      HierarchicalAdviceExperiment.Advice (S o) r) := by
  infer_instance
theorem expectedMeeting_ge_gamma_oai
    (hmass : InitialParameters.simultaneous δ / 2 ≤
      usefulMass parameters i j hij input strategy)
    (hpaired : pairedVariation parameters i j hij input strategy ≤ 10 * parameters.accuracy)
    (hcoarse : coarseVariation parameters i j hij input strategy ≤ 10 * parameters.accuracy) :
    FixedRankContradiction.gamma parameters (j.val + 1) ≤
      expectedMeeting parameters i j hij input strategy := by
  have hheight (o : Outer parameters j input) :
      Nodes.height (experiment parameters i j hij input strategy o).upper = j.val + 1 :=
    StoppedProjectedExperiment.upper_height (Nat.succ_le_of_lt j.isLt) o
  have hbound := HierarchicalFixedAdviceFamily.prediction_difference parameters
    (experiment parameters i j hij input strategy) (outerLaw parameters j input)
    (externalLaw parameters i j hij input) (background parameters i j hij input)
    (scalarLaw parameters i j hij input) (backgrounds parameters i j hij input strategy)
    (j.val + 1) (Nat.succ_le_of_lt j.isLt) hheight hmass hpaired hcoarse
  have hmeeting := HierarchicalProjectedOuterAverage.expectedMeeting_ge_prediction_difference
    parameters.plan (StoppedProjectedExperiment.nativeSlots (clauses input))
    (StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij (designated parameters i))
    (StoppedProjectedExperiment.projection (clauses input) (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij (designated parameters i))
    (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt)) (i.val + 1)
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij)
    (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij)
    (fun _ => StoppedProjectedExperiment.innerLaw (FixedRows.rows parameters.plan) hij
      (fun k _ => FixedParameters.branch_pos parameters k)
      (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
      (FixedStoppedDecoderLaw.flag parameters i))
    (outerLaw parameters j input) (FixedStoppedDecoderLaw.labeling parameters input strategy)
    hδ (FixedRows.rows parameters.plan (j.val + 1))
    (fun o => congrArg (FixedRows.rows parameters.plan)
      (StoppedProjectedExperiment.upper_height (Nat.succ_le_of_lt j.isLt) o))
  calc
    _ = HierarchicalProjectedOuterAverage.factor parameters.plan
        (FixedRows.rows parameters.plan (j.val + 1)) *
        UpperParameterScalars.b (InitialParameters.useful δ) parameters.plan.density
          (InitialParameters.inverse δ) parameters.plan.order
          (FixedRows.rows parameters.plan (j.val + 1)) :=
      (HierarchicalProjectedOuterAverage.factor_mul_b_eq_gamma parameters.plan _).symm
    _ ≤ HierarchicalProjectedOuterAverage.factor parameters.plan
        (FixedRows.rows parameters.plan (j.val + 1)) *
        HierarchicalFixedAdviceFamily.predictionDifference parameters
          (experiment parameters i j hij input strategy) (outerLaw parameters j input) :=
      mul_le_mul_of_nonneg_left hbound
        (HierarchicalProjectedOuterAverage.factor_nonneg parameters.plan _)
    _ ≤ _ := hmeeting

end
end PerfectCompleteness.FixedStoppedInverseBound

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedInverseBound.expectedMeeting_ge_gamma_oai := @OAI.PerfectCompleteness.FixedStoppedInverseBound.expectedMeeting_ge_gamma_oai
