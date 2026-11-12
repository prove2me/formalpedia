-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedMeetingEquality.physical_expectation_eq_expectedMeeting
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:23:55.314658+00:00
-- url     : https://prove2.me/submissions/04d3d5bd-87b5-476a-8bfa-78b878dbe8de

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
import Theorems.Thm_OAI_PerfectCompleteness_SourcePhysicalSourceSwap_expectation_swap
import Theorems.Thm_OAI_PerfectCompleteness_StoppedProjectedExperiment_physicalFiber_probability
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DependentPredictionDifferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

theorem pushforward_fiber {S : Type*} [Fintype S] {X Y : S → Type*}
    [∀ s, Fintype (X s)] [∀ s, Fintype (Y s)]
    (μ : FiniteDistribution S) (P : (s : S) → FiniteDistribution (X s))
    (f : (s : S) → X s → Y s) :
    (sigmaLaw μ P).pushforward (fun x => (⟨x.1, f x.1 x.2⟩ : Σ s, Y s)) =
      sigmaLaw μ (fun s => (P s).pushforward (f s)) := by
  apply eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, sigmaLaw_probability, sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro s
  rw [FiniteDistribution.probability_pushforward]

end
end PerfectCompleteness.SigmaObservation

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

end
end PerfectCompleteness.HierarchicalProjectedExperiment


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_StoppedOwnInputGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedOwnInputGeometry

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RelativeDescendantProducts
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n : Nat}

theorem pathTapeEquiv_law {t : Nat} (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (h : p = q) :
    (WholeArraySampler.tapeLaw rows repeats p.2 slots).pushforward
        (pathTapeEquiv rows repeats slots h) =
      WholeArraySampler.tapeLaw rows repeats q.2 slots := by
  cases h
  exact FiniteDistribution.pushforward_id _

end
end PerfectCompleteness.StoppedOwnInputGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedExperiment
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedExperiment

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RelativeDescendantProducts
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

theorem tapeRead_law (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    (tapeLaw clauses rows repeats hupper hij designated hbranch hrows flag o).pushforward
        (tapeRead clauses rows repeats hupper hij designated o) =
      (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).original := by
  calc
    _ = CompletionSoundness.sigmaLaw (innerLaw rows hij hbranch hrows flag) (fun k =>
        (WholeArraySampler.tapeLaw rows repeats (stoppedPath rows hupper hij o k)
          (projectedSlots clauses rows hupper hij designated o k)).pushforward
            (StoppedOwnInputGeometry.pathTapeEquiv rows repeats
              (projectedSlots clauses rows hupper hij designated o k)
              (fullPath_spec rows hupper hij o k).symm)) :=
      SigmaObservation.pushforward_fiber (innerLaw rows hij hbranch hrows flag)
        (fun k => WholeArraySampler.tapeLaw rows repeats (stoppedPath rows hupper hij o k)
          (projectedSlots clauses rows hupper hij designated o k))
        (fun k tape => StoppedOwnInputGeometry.pathTapeEquiv rows repeats
          (projectedSlots clauses rows hupper hij designated o k)
          (fullPath_spec rows hupper hij o k).symm tape)
    _ = _ :=
      congrArg (fun kernel :
          (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) →
            FiniteDistribution (WholeArraySampler.Tape rows repeats
              (WholeArrayInteriorOwnInputLaw.fullPath (upper hupper o)
                (lower rows hupper hij o k) (cut rows hupper hij o k))
              (projectedSlots clauses rows hupper hij designated o k)) =>
        CompletionSoundness.sigmaLaw (innerLaw rows hij hbranch hrows flag) kernel)
        (funext (fun k => StoppedOwnInputGeometry.pathTapeEquiv_law rows repeats
          (projectedSlots clauses rows hupper hij designated o k)
          (fullPath_spec rows hupper hij o k).symm))

section Physical

variable [NeZero m]

omit [NeZero m] in
theorem physicalRead_law
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    (physicalLaw clauses rows repeats hupper hij designated hbranch hrows flag o).pushforward
        (physicalRead clauses rows repeats hupper hij designated o) =
      tapeLaw clauses rows repeats hupper hij designated hbranch hrows flag o := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, physicalLaw,
    CompletionSoundness.sigmaLaw_probability, tapeLaw, CompletionSoundness.sigmaLaw_probability]
  simp only [physicalBaseLaw, innerLaw, SourceProjectedTag.law,
    FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro pref
  apply FiniteDistribution.expectation_congr
  intro positions
  calc
    _ = (CanonicalDirections.law rows n hrows).expectation (fun directions =>
        (SourceProjectedTag.flagLaw flag).expectation (fun flags =>
          (WholeArraySampler.tapeLaw rows repeats
            (stoppedPath rows hupper hij o (withFlags rows (pref, (positions, directions)) flags))
            (projectedSlots clauses rows hupper hij designated o
              (withFlags rows (pref, (positions, directions)) flags))).probability
                (fun tape => event ⟨withFlags rows (pref, (positions, directions)) flags, tape⟩))) := by
      apply FiniteDistribution.expectation_congr
      intro directions
      exact physicalFiber_probability clauses rows repeats hupper hij designated flag o
        (pref, (positions, directions)) event
    _ = _ := FiniteDistribution.expectation_comm _ _ _

omit [NeZero m] in
theorem physicalExperimentRead_law
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) :
    (physicalLaw clauses rows repeats hupper hij designated hbranch hrows flag o).pushforward
        (physicalExperimentRead clauses rows repeats hupper hij designated o) =
      (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).original := by
  change (physicalLaw clauses rows repeats hupper hij designated hbranch hrows flag o).pushforward
    (fun sample => tapeRead clauses rows repeats hupper hij designated o
      (physicalRead clauses rows repeats hupper hij designated o sample)) = _
  rw [← FiniteDistribution.pushforward_comp, physicalRead_law]
  exact tapeRead_law clauses rows repeats hupper hij designated hbranch hrows flag σ o

end Physical

end
end PerfectCompleteness.StoppedProjectedExperiment

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedPhysicalAdvice
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedPhysicalAdvice

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

variable [NeZero m]
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

include σ

attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedPhysicalAdvice.adviceFintype
attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedPhysicalAdvice.physicalAdviceFintype
attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedPhysicalAdvice.rawFiberFintype
omit [NeZero m] in
theorem fiber_read_law
    (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat) :
    ((StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
        (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o).product
      (FiniteDistribution.uniform (Advice rows hupper o r))).pushforward
        (fun x => HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
          (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
          (StoppedProjectedExperiment.upper hupper o)
          (StoppedProjectedExperiment.lower rows hupper hij o)
          (StoppedProjectedExperiment.cut rows hupper hij o) r
          (StoppedProjectedExperiment.physicalExperimentRead
            clauses rows repeats hupper hij designated o x.1, x.2)) =
      HierarchicalProjectedExperiment.rawLaw (rows := rows) (repeats := repeats)
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o)
        (StoppedProjectedExperiment.cut rows hupper hij o)
        (StoppedProjectedExperiment.innerLaw rows hij
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag) r := by
  let μ := StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o
  let ν := FiniteDistribution.uniform (Advice rows hupper o r)
  let readTape := StoppedProjectedExperiment.physicalExperimentRead
    clauses rows repeats hupper hij designated o
  let readRaw := HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
    (StoppedProjectedExperiment.upper hupper o)
    (StoppedProjectedExperiment.lower rows hupper hij o)
    (StoppedProjectedExperiment.cut rows hupper hij o) r
  have hprod := FiniteDistribution.product_pushforward μ ν readTape (id : Advice rows hupper o r → _)
  rw [FiniteDistribution.pushforward_id] at hprod
  have hcomp := FiniteDistribution.pushforward_comp (μ.product ν)
    (fun x => (readTape x.1, (id : Advice rows hupper o r → _) x.2)) readRaw
  have hphysical := StoppedProjectedExperiment.physicalExperimentRead_law
    clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag σ o
  change μ.pushforward readTape = _ at hphysical
  have hraw := HierarchicalProjectedExperiment.rawRead_law (rows := rows) (repeats := repeats)
    (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
    (StoppedProjectedExperiment.upper hupper o)
    (StoppedProjectedExperiment.lower rows hupper hij o)
    (StoppedProjectedExperiment.cut rows hupper hij o)
    (StoppedProjectedExperiment.innerLaw rows hij
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag) r
  have hprodRaw := congrArg
    (fun P : FiniteDistribution
      (HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o)
        (StoppedProjectedExperiment.cut rows hupper hij o) × Advice rows hupper o r) =>
      P.pushforward readRaw) hprod
  have hphysicalRaw := congrArg
    (fun P : FiniteDistribution
      (HierarchicalProjectedExperiment.Sample (rows := rows) (repeats := repeats)
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o)
        (StoppedProjectedExperiment.cut rows hupper hij o)) =>
      (P.product ν).pushforward readRaw) hphysical
  exact hcomp.symm.trans (hprodRaw.trans (hphysicalRaw.trans hraw))

theorem read_law (r : Nat) :
    (law (t := t) clauses rows repeats hupper hij designated hbranch hrows flag r).pushforward
        (read (t := t) clauses rows repeats hupper hij designated r) =
      rawLaw (t := t) clauses rows repeats hupper hij designated hbranch hrows flag r := by
  have hsplit := SigmaObservation.pushforward_fiber
    (X := fun o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m) =>
      StoppedProjectedExperiment.PhysicalSample clauses rows repeats hupper hij designated o ×
        Advice rows hupper o r)
    (Y := fun o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m) =>
      HierarchicalProjectedExperiment.RawSample (rows := rows) (repeats := repeats)
        (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
        (StoppedProjectedExperiment.upper hupper o)
        (StoppedProjectedExperiment.lower rows hupper hij o)
        (StoppedProjectedExperiment.cut rows hupper hij o) r)
    (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch)
    (fun o => (StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o).product
        (FiniteDistribution.uniform (Advice rows hupper o r)))
    (fun o x => HierarchicalProjectedExperiment.rawRead (rows := rows) (repeats := repeats)
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o)
      (StoppedProjectedExperiment.upper hupper o)
      (StoppedProjectedExperiment.lower rows hupper hij o)
      (StoppedProjectedExperiment.cut rows hupper hij o) r
      (StoppedProjectedExperiment.physicalExperimentRead
        clauses rows repeats hupper hij designated o x.1, x.2))
  exact hsplit.trans (congrArg
    (CompletionSoundness.sigmaLaw (StoppedProjectedExperiment.outerLaw (t := t) (m := m) hupper hbranch))
    (funext (fun o => fiber_read_law clauses rows repeats hupper hij designated
      hbranch hrows flag σ o r)))

theorem expectation_read (r : Nat)
    (value : RawSample (t := t) clauses rows repeats hupper hij designated r → ℝ) :
    (law clauses rows repeats hupper hij designated hbranch hrows flag r).expectation
        (fun sample => value (read clauses rows repeats hupper hij designated r sample)) =
      (rawLaw clauses rows repeats hupper hij designated hbranch hrows flag r).expectation value := by
  rw [← read_law clauses rows repeats hupper hij designated hbranch hrows flag σ r]
  exact (FiniteDistribution.expectation_pushforward _ _ _).symm

end
end PerfectCompleteness.StoppedProjectedPhysicalAdvice

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedPhysicalPrefixSwap
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedPhysicalPrefixSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

variable {branch : Nat → Nat} {n i j t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)

omit [NeZero m] in
theorem fiber_expectation
    (o : StoppedProjectedPhysicalAdvice.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m)) (r : Nat)
    (F : StoppedProjectedPhysicalAdvice.Sample
      clauses rows repeats hupper hij designated r → ℝ) :
    (StoppedProjectedExperiment.physicalLaw clauses rows repeats hupper hij designated
      (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag o).expectation
        (fun sample => (FiniteDistribution.uniform
          (StoppedProjectedPhysicalAdvice.Advice rows hupper o r)).expectation
            (fun A => F ⟨o, (sample, A)⟩)) =
      (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le)
        (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper))).expectation
          (fun lower => (FiniteDistribution.uniform
            (StoppedProjectedPhysicalAdvice.Advice rows hupper o r)).expectation
              (fun A => (CanonicalDirections.law rows n hrows).expectation
                (fun directions => (SourceProjectedTag.positionLaw
                  (branch := branch) (n := i) (t := t)).expectation
                    (fun positions => (StoppedProjectedExperiment.physicalFiberLaw
                      clauses rows repeats hupper hij designated flag o
                        (lower, (positions, directions))).expectation
                          (fun raw => F ⟨o, (⟨(lower, (positions, directions)), raw⟩, A)⟩))))) := by
  rw [FiniteDistribution.expectation_comm]
  simp only [StoppedProjectedExperiment.physicalLaw, CandidateCoupling.expectation_sigmaLaw,
    StoppedProjectedExperiment.physicalBaseLaw, FiniteDistribution.expectation_product]
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro lower
  apply FiniteDistribution.expectation_congr
  intro A
  exact FiniteDistribution.expectation_comm _ _ _

theorem expectation_prefixes (r : Nat)
    (F : StoppedProjectedPhysicalAdvice.Sample
      clauses rows repeats hupper hij designated r → ℝ) :
    (StoppedProjectedPhysicalAdvice.law clauses rows repeats hupper hij designated
      hbranch hrows flag r).expectation F =
      ((GeometricCutSplit.prefixLaw hupper hbranch).product
        (GeometricCutSplit.prefixLaw (Nat.succ_le_succ hij.le)
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)))).expectation
            (fun prefixes => (PreliminarySampler.questionsLaw
              (branch := branch) (n := n) (t := t) (m := m)).expectation
                (fun Q => (FiniteDistribution.uniform
                  (StoppedProjectedPhysicalAdvice.Advice rows hupper (Q, prefixes.1) r)).expectation
                    (fun A => (CanonicalDirections.law rows n hrows).expectation
                      (fun directions => (SourceProjectedTag.positionLaw
                        (branch := branch) (n := i) (t := t)).expectation
                          (fun positions => (StoppedProjectedExperiment.physicalFiberLaw
                            clauses rows repeats hupper hij designated flag (Q, prefixes.1)
                              (prefixes.2, (positions, directions))).expectation
                                (fun raw => F ⟨(Q, prefixes.1),
                                  (⟨(prefixes.2, (positions, directions)), raw⟩, A)⟩)))))) := by
  rw [StoppedProjectedPhysicalAdvice.law, CandidateCoupling.expectation_sigmaLaw]
  simp only [StoppedProjectedExperiment.outerLaw, FiniteDistribution.expectation_product]
  simp_rw [fiber_expectation clauses rows repeats hupper hij designated hbranch hrows flag]
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro upper
  exact FiniteDistribution.expectation_comm _ _ _

end
end PerfectCompleteness.StoppedPhysicalPrefixSwap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FixedStoppedPhysicalLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedPhysicalLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

theorem expectation_read (value : PhysicalSample parameters i j hij input → ℝ) :
    (physicalLaw parameters i j hij input).expectation value =
      (law parameters i j hij input).expectation
        (fun sample => value (read parameters i j hij input sample)) := by
  refine (StoppedPhysicalPrefixSwap.expectation_prefixes
    (t := FixedRows.sourceLength parameters.plan hδ)
    (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => parameters.plan.rows_pos (parameters.plan.depth - (k + 1)))
    (flag parameters i) parameters.plan.order value).trans ?_
  simp only [law, FixedStoppedDecoderContext.law, CandidateCoupling.expectation_sigmaLaw,
    FixedStoppedDecoderContext.fiberLaw]
  apply FiniteDistribution.expectation_congr
  intro pref
  simp only [FiniteDistribution.expectation_product]
  let questionLaw := PreliminarySampler.questionsLaw
    (branch := FixedParameters.branch parameters) (n := parameters.plan.depth)
    (t := FixedRows.sourceLength parameters.plan hδ)
    (m := (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length)
  let adviceLaw := FiniteDistribution.uniform (FixedStoppedDecoderContext.Advice parameters i j pref)
  let directionsLaw := FixedStoppedDecoderContext.directionLaw parameters
  let outsideLaw := FiniteDistribution.uniform
    (FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
  let statistic := fun
      (questions : PreliminarySampler.Questions (FixedParameters.branch parameters)
        parameters.plan.depth (FixedRows.sourceLength parameters.plan hδ)
        (PCPSource.normalizedFormula (BinaryLanguage.totalRename input)).clauses.length)
      (A : FixedStoppedDecoderContext.Advice parameters i j pref)
      (directions : FixedStoppedDecoderContext.Directions parameters) =>
    (SourceProjectedTag.positionLaw (branch := FixedParameters.branch parameters)
      (n := i.val) (t := FixedRows.sourceLength parameters.plan hδ)).expectation
        (fun positions => (StoppedProjectedExperiment.physicalFiberLaw
          (clauses input) (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij (designated parameters i) (flag parameters i)
          (questions, pref.1) (pref.2, (positions, directions))).expectation
            (fun raw => value ⟨(questions, pref.1), (⟨(pref.2, (positions, directions)), raw⟩, A)⟩))
  let rebuilt := fun (external : FixedStoppedDecoderContext.OutsideQuestions parameters i j hij input pref)
      (A : FixedStoppedDecoderContext.Advice parameters i j pref)
      (directions : FixedStoppedDecoderContext.Directions parameters) =>
    (FiniteDistribution.uniform
      (FixedStoppedDecoderContext.Exterior parameters i j hij input pref external)).expectation
        (fun exterior => (childLaw parameters i j hij input pref).expectation
          (fun sample => value (read parameters i j hij input
            ⟨⟨pref, external, A, directions, exterior⟩, sample⟩)))
  change questionLaw.expectation (fun questions => adviceLaw.expectation (fun A =>
      directionsLaw.expectation (fun directions => statistic questions A directions))) =
    outsideLaw.expectation (fun external => adviceLaw.expectation (fun A =>
      directionsLaw.expectation (fun directions => rebuilt external A directions)))
  calc
    _ = adviceLaw.expectation (fun A => directionsLaw.expectation (fun directions =>
        questionLaw.expectation (fun questions => statistic questions A directions))) := by
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro A
      exact FiniteDistribution.expectation_comm _ _ _
    _ = adviceLaw.expectation (fun A => directionsLaw.expectation (fun directions =>
        outsideLaw.expectation (fun external => rebuilt external A directions))) := by
      apply FiniteDistribution.expectation_congr
      intro A
      apply FiniteDistribution.expectation_congr
      intro directions
      exact SourcePhysicalSourceSwap.expectation_swap (clauses input)
        (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
        (path parameters i j hij pref) (designated parameters i) (flag parameters i)
        (fun questions positions exterior raw =>
          value ⟨(questions, pref.1), (⟨(pref.2, (positions, directions)), (exterior, raw)⟩, A)⟩)
    _ = _ := by
      calc
        _ = adviceLaw.expectation (fun A => outsideLaw.expectation (fun external =>
            directionsLaw.expectation (fun directions => rebuilt external A directions))) := by
          apply FiniteDistribution.expectation_congr
          intro A
          exact FiniteDistribution.expectation_comm _ _ _
        _ = _ := FiniteDistribution.expectation_comm _ _ _

theorem read_law :
    (law parameters i j hij input).pushforward (read parameters i j hij input) =
      physicalLaw parameters i j hij input := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward,
    CandidateCoupling.probability_eq_expectation, CandidateCoupling.probability_eq_expectation]
  exact (expectation_read parameters i j hij input (fun sample => if event sample then 1 else 0)).symm

end
end PerfectCompleteness.FixedStoppedPhysicalLaw

end

section

namespace PerfectCompleteness.FixedStoppedNativeLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype

section PathTransport

variable {branch : Nat → Nat} {root h t v m : Nat}
  (rows repeats : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  {p q : Path branch root (h + 1)}

theorem sourceSampleEquiv_law [NeZero m] (hp : p = q)
    (flag : Fin (branch h) → FiniteDistribution Bool) :
    (SourceChildKernel.originalLaw (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated flag).pushforward
        (sourceSampleEquiv rows repeats clauses designated hp) =
      SourceChildKernel.originalLaw (C := WholeCutCalls.Index rows repeats q) (t := t)
        rows clauses designated flag := by
  cases hp
  exact FiniteDistribution.pushforward_id _

end PathTransport

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

attribute [local instance] OAI.PerfectCompleteness.FixedStoppedNativeLaw.contextAdviceFintype
theorem childRead_law (context : Context parameters i j hij input) :
    (CleanDecoderRate.rawLaw (setup parameters i j hij input context)
      (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val)).pushforward
        (childRead parameters i j hij input context) =
      FixedStoppedPhysicalLaw.childLaw parameters i j hij input context.1 :=
  sourceSampleEquiv_law (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (FixedStoppedPhysicalLaw.clauses input) (FixedStoppedPhysicalLaw.designated parameters i)
    (path_eq parameters i j hij input context) (FixedStoppedPhysicalLaw.flag parameters i)

theorem sourceRead_law :
    (law parameters i j hij input).pushforward (sourceRead parameters i j hij input) =
      FixedStoppedPhysicalLaw.law parameters i j hij input := by
  have hsplit := SigmaObservation.pushforward_fiber
    (X := fun context : Context parameters i j hij input =>
      CleanDecoderRate.Sample (setup parameters i j hij input context))
    (Y := fun context : Context parameters i j hij input =>
      FixedStoppedPhysicalLaw.ChildSample parameters i j hij input context.1)
    (FixedStoppedDecoderContext.law parameters i j hij input)
    (fun context => CleanDecoderRate.rawLaw (setup parameters i j hij input context)
      (parameters.cubeSize i.val) (FixedDecoderCleanRate.cubePositive parameters i.val))
    (fun context => childRead parameters i j hij input context)
  exact hsplit.trans (congrArg
    (fun P : (context : Context parameters i j hij input) →
        FiniteDistribution (FixedStoppedPhysicalLaw.ChildSample parameters i j hij input
          context.1) =>
      CompletionSoundness.sigmaLaw (FixedStoppedDecoderContext.law parameters i j hij input) P)
    (funext (fun context => childRead_law parameters i j hij input context)))

theorem read_law :
    (law parameters i j hij input).pushforward (read parameters i j hij input) =
      FixedStoppedPhysicalLaw.physicalLaw parameters i j hij input := by
  change (law parameters i j hij input).pushforward
    (fun sample => FixedStoppedPhysicalLaw.read parameters i j hij input
      (sourceRead parameters i j hij input sample)) = _
  rw [← FiniteDistribution.pushforward_comp, sourceRead_law]
  exact FixedStoppedPhysicalLaw.read_law parameters i j hij input

theorem expectation_read
    (value : FixedStoppedPhysicalLaw.PhysicalSample parameters i j hij input → ℝ) :
    (law parameters i j hij input).expectation
        (fun sample => value (read parameters i j hij input sample)) =
      (FixedStoppedPhysicalLaw.physicalLaw parameters i j hij input).expectation value := by
  rw [← read_law parameters i j hij input, FiniteDistribution.expectation_pushforward]

end
end PerfectCompleteness.FixedStoppedNativeLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedProjectedMeetingLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedMeetingLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] StoppedProjectedPhysicalAdvice.adviceFintype
  StoppedProjectedPhysicalAdvice.physicalAdviceFintype
  StoppedProjectedPhysicalAdvice.rawFiberFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ)

variable {branch : Nat → Nat} {i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (hupper : j + 1 ≤ plan.depth) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

variable [NeZero m]
  (hbranch : ∀ k < plan.depth, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))

theorem expectation_meetingProbability :
    (StoppedProjectedPhysicalAdvice.law clauses (FixedRows.rows plan)
      (FixedRows.repeats plan) hupper hij designated hbranch
      (rows_positive plan) flag plan.order).expectation
        (meetingProbability plan clauses hupper hij designated hbranch flag σ) =
      expectedMeeting plan clauses hupper hij designated hbranch flag σ := by
  unfold meetingProbability
  rw [StoppedProjectedPhysicalAdvice.expectation_read clauses (FixedRows.rows plan)
    (FixedRows.repeats plan) hupper hij designated hbranch
    (rows_positive plan) flag σ plan.order]
  simp only [StoppedProjectedPhysicalAdvice.rawLaw, expectedMeeting,
    HierarchicalProjectedOuterAverage.expectedMeeting,
    CandidateCoupling.expectation_sigmaLaw,
    HierarchicalProjectedAverage.expectedMeeting, rawMeetingProbability]

end
end PerfectCompleteness.StoppedProjectedMeetingLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedMeetingEquality
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerNode_height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedMeetingEquality

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.scalarFintype

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

theorem flag_eq :
    FixedStoppedDecoderLaw.flag parameters i = FixedStoppedPhysicalLaw.flag parameters i := by
  funext child
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  cases b <;> simp [FixedStoppedDecoderLaw.flag, FixedStoppedPhysicalLaw.flag,
    ProjectionPosterior.bernoulli, ProjectedCleanRate.projectionFlag,
    RepetitionRate.bernoulli, ProjectedCleanRate.projectionDensity,
    FixedParameters.projectionProbability]

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

local instance physicalLeftFintype_rf2de68_1 {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual (ZMod 2) (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
theorem physical_expectation_eq_expectedMeeting_oai :
    (FixedStoppedNativeLaw.law parameters i j hij input).expectation
        (physicalMeetingProbability parameters i j hij input strategy) =
      expectedMeeting parameters i j hij input strategy := by
  unfold physicalMeetingProbability
  rw [FixedStoppedNativeLaw.expectation_read]
  unfold expectedMeeting
  rw [flag_eq parameters i]
  exact StoppedProjectedMeetingLaw.expectation_meetingProbability parameters.plan
    (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (FixedStoppedPhysicalLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)

end
end PerfectCompleteness.FixedStoppedMeetingEquality

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedMeetingEquality.physical_expectation_eq_expectedMeeting_oai := @OAI.PerfectCompleteness.FixedStoppedMeetingEquality.physical_expectation_eq_expectedMeeting_oai
