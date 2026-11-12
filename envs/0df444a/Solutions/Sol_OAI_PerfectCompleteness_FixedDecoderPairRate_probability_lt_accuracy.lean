-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedDecoderPairRate.probability_lt_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:21:45.261736+00:00
-- url     : https://prove2.me/submissions/4900d954-09f6-453d-a0e1-3b597b71dd1a

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
import Definitions.Def_PerfectCompleteness
import Definitions.Def_OAIQ252P018
import Theorems.Thm_OAI_PerfectCompleteness_CleanDecoderRate_bound
import Theorems.Thm_OAI_PerfectCompleteness_SourceOddLists_repetition_halfRate

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_NameCompaction
attribute [-instance] _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeBEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_extend _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_restrict _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.fromReduction_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_bits _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.raw_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceClause.localEval_restrict _root_.OAI.PerfectCompleteness.SourceClauseReaderMachine.clauseShape_eq _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.body_nil _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.recordWords_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.records_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.words_length _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_dart _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.card_vertex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
An explicit name compaction for finite three-literal CNF formulas. Only the
occurring names are scanned: the declared variable count is never enumerated.
Both assignment transports preserve every clause evaluation and therefore
every finite clause-score gap. The encoding bound is a size theorem; a machine
running-time bound and the constant-gap PCP construction remain separate.
-/

namespace UniqueGamesTheorem.Foundations.PCP.NameCompaction

open UniqueGamesTheorem.Foundations.Target

theorem failureCount_evaluations (F : Formula) (A : Fin F.variables → Bool)
    (indices : List (Fin F.clauses.length)) :
    failureCount F A indices =
      (indices.map (fun i => (clauseAt F i).eval A)).count false := by
  induction indices with
  | nil => simp [failureCount]
  | cons i rest ih =>
    cases h : (clauseAt F i).eval A <;>
      simp [failureCount, clauseFailure, h, ih, Nat.add_comm]

/-- The semantic score is the checked verifier's actual failed-clause count. -/
theorem verifier_failureCount (F : Formula) (A : Fin F.variables → Bool) :
    failureCount F A (allIndices F) = failedCount F A := by
  rw [failureCount_evaluations, evaluations_allIndices]
  rfl

end UniqueGamesTheorem.Foundations.PCP.NameCompaction

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_KeyFiniteness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalEdges.coarsen_evaluateLabel _root_.OAI.PerfectCompleteness.CanonicalEdges.restore_coarsen _root_.OAI.PerfectCompleteness.CanonicalKeyShape.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalKeyShape.transport_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_decode _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_symm_val _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecursiveSamplerLaws
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteProduct

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem eval_pushforward (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (law P).pushforward (fun x => x i) = P i := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  calc
    _ = (law P).expectation (fun x => if x i = a then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
    _ = (P i).expectation (fun b => if b = a then 1 else 0) :=
      expectation_eval P i (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [FiniteDistribution.expectation, mul_ite]

end
end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DependentDecoderSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DependentDecoderSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Q₁ Q₂ E : Type*} [Fintype Q₁] [Fintype Q₂] [Fintype E]
  [DecidableEq Q₁] [DecidableEq Q₂]
  {A : Q₁ → Type*} {B : Q₂ → Type*}
  [∀ q, Fintype (A q)] [∀ q, Fintype (B q)]

theorem read_law (leftKernel : (q : Q₁) → FiniteDistribution (A q))
    (rightKernel : (q : Q₂) → FiniteDistribution (B q)) (q₁ : Q₁) (q₂ : Q₂) :
    (seedLaw leftKernel rightKernel).pushforward (fun seed => (seed.1 q₁, seed.2 q₂)) =
      (leftKernel q₁).product (rightKernel q₂) := by
  have h := FiniteDistribution.product_pushforward
    (FiniteProduct.law leftKernel) (FiniteProduct.law rightKernel)
    (fun table : (q : Q₁) → A q => table q₁)
    (fun table : (q : Q₂) → B q => table q₂)
  rw [FiniteProduct.eval_pushforward, FiniteProduct.eval_pushforward] at h
  exact h

end
end PerfectCompleteness.DependentDecoderSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionOrderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
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

theorem bound_pos (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    0 < bound branch n t calls rows :=
  lt_of_lt_of_le (Nat.card_pos (α := Raw calls rows slots)) (card_le calls rows slots)

end
end PerfectCompleteness.ChildBlockCardinality


end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_AlphabetTableBoundsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

open Target

theorem convert_gap {q : Nat} (V : FiniteVerifier q) (hq : 3 ≤ q) (a b : Nat)
    (gap : ∀ A, a * V.events ≤ b * rejectedEventCount V A)
    (B : Fin (outputVariables V) → Bool) :
    a * (convert V hq).clauses.length ≤
      (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by
  have eventGap := gap (restrictAssignment V B)
  have countBound := Nat.mul_le_mul_left b (convert_count_bridge V hq B)
  rw [convert_clause_count]
  calc
    a * (V.events * (2 ^ q * (q - 2))) = (a * V.events) * (2 ^ q * (q - 2)) := by
      rw [Nat.mul_assoc]
    _ ≤ (b * NameCompaction.failedCount (convert V hq) B) * (2 ^ q * (q - 2)) :=
      Nat.mul_le_mul_right _ (eventGap.trans countBound)
    _ = (b * (2 ^ q * (q - 2))) * NameCompaction.failedCount (convert V hq) B := by ac_rfl

end UniqueGamesTheorem.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_NormalizationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.Normalization

open UniqueGamesTheorem.Foundations
open Target
open SourceClause

theorem normalize_gap (F : Formula) (a b : Nat)
    (gap : ∀ A, a * F.clauses.length ≤ b * PCP.NameCompaction.failedCount F A)
    (B : Fin (normalize F).variables → Bool) :
    a * (normalize F).clauses.length ≤
      (13 * b) * PCP.NameCompaction.failedCount (normalize F) B := by
  have hsource := gap (restrictAssignment F B)
  have hcount := Nat.mul_le_mul_left b (failedCount_domination F B)
  rw [normalize_clause_count]
  calc
    a * (13 * F.clauses.length) = 13 * (a * F.clauses.length) := by ac_rfl
    _ ≤ 13 * (b * PCP.NameCompaction.failedCount (normalize F) B) :=
      Nat.mul_le_mul_left 13 (hsource.trans hcount)
    _ = (13 * b) * PCP.NameCompaction.failedCount (normalize F) B := by ac_rfl

end PerfectCompleteness.Normalization



end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalBooleanVerifier
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.Normalization.equalityClauses_length _root_.OAI.PerfectCompleteness.Normalization.extend_copyVariable _root_.OAI.PerfectCompleteness.Normalization.extend_oldVariable _root_.OAI.PerfectCompleteness.Normalization.gadgetClauses_length _root_.OAI.PerfectCompleteness.Normalization.gadget_length _root_.OAI.PerfectCompleteness.Normalization.normalize_clause_count _root_.OAI.PerfectCompleteness.Normalization.normalize_variables _root_.OAI.PerfectCompleteness.Normalization.restrict_extend _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.fromReduction_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_bits _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.raw_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceClauseReaderMachine.clauseShape_eq _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.body_nil _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.recordWords_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.records_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.words_length _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFPattern.tableGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_current _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_field _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceContextLoad.coordinateOutput_remaining _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceGame.baseGame_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.nBits_eq _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceOccurrences.rawSourceList_length _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceSoundness.leftTable_answer _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_dummy _root_.OAI.UniqueGamesTheorem.Foundations.Hastad.SourceStartup.ready_leftBlock _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.clause_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.FinalTableFormula.variable_count _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_false _root_.OAI.UniqueGamesTheorem.Foundations.PCP.LazyConstraint.edgeSatisfied_true _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_portGraph _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.constraintGraph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Overlay.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Preprocessing.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudRank_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_oldCloudIndex _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingCloudIndex.cloudSelect_val _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingOverlayTables.accepts_materialize _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.accepts_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.baseGraph_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingPaddingTables.rotation_pad _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularTables.accepts_ofCloudTables _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseInput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_cons _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineLoopData.clauseOutput_nil _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_field _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_input _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialMachineReadClause.recordTapes_name _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices _root_.OAI.UniqueGamesTheorem.Foundations.PCP.Regularization.graph_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.edgeSatisfied_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inl _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_reverse_inr _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.pad_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.VertexPadding.paddedG_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

open Target

variable {V E : Type*} {n m : Nat}

theorem cnf_gap [Fintype E] (G : ConstraintGraph V E Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : Nat)
    (source : ∀ labeling : V → Label, a * Fintype.card E ≤ b * G.rejectionCount labeling)
    (assignment : OutputAssignment G vertices edges) :
    a * (cnf G vertices edges).clauses.length ≤
      (b * 40960) * NameCompaction.failedCount (cnf G vertices edges) assignment := by
  have cardEdges : Fintype.card E = m := by simpa using Fintype.card_congr edges
  have testGap (bits : Fin (n * 6) → Bool) :
      a * m ≤ b * VerifierToCNF.rejectedEventCount (verifier G vertices edges) bits := by
    rw [rejection_count_eq]
    simpa only [cardEdges] using source (labelsOfBits vertices bits)
  simpa only [cnf, VerifierToCNF.twelve_query_factor] using
    VerifierToCNF.convert_gap (verifier G vertices edges) (by decide) a b testGap assignment

end UniqueGamesTheorem.Foundations.PCP.FinalBooleanVerifier

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_SourceGapLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace UniqueGamesTheorem.Foundations.Hastad.SourceNonempty

open Target PCP

/-- Convert an actual natural-number clause-count inequality to the real
inequality used by the clause-variable game. -/
theorem real_clause_gap_of_count (F : Formula) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.variables → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment)
    (assignment : Fin F.variables → Bool) :
    (a : ℝ) / (b : ℝ) * F.clauses.length ≤
      (failureCount F assignment (allIndices F) : ℝ) := by
  rw [NameCompaction.verifier_failureCount]
  have hreal : (a : ℝ) * F.clauses.length ≤
      (b : ℝ) * (NameCompaction.failedCount F assignment : ℝ) := by
    exact_mod_cast hgap assignment
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (Nat.cast_pos.mpr hb)).mpr
  simpa only [mul_comm] using hreal

theorem clauseGap_of_count (F : Formula) (a b : ℕ) (hne : F.clauses ≠ [])
    (hb : 0 < b)
    (hgap : ∀ assignment : Fin F.variables → Bool,
      a * F.clauses.length ≤ b * NameCompaction.failedCount F assignment) :
    SourceGap.ClauseGap F ((a : ℚ) / (b : ℚ)) := by
  refine ⟨hne, fun assignment => ?_⟩
  simpa only [Rat.cast_div, Rat.cast_natCast] using
    real_clause_gap_of_count F a b hb hgap assignment

variable {V E : Type*} {n m : ℕ}

/-- The actual final graph bundle carries a nonempty dart type, so its
explicitly numbered Boolean CNF is nonempty even before using any gap. -/
theorem cnf_nonempty_of_nonempty_darts [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) :
    (FinalBooleanVerifier.cnf G vertices edges).clauses ≠ [] := by
  have hcard : Fintype.card E = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr edges
  have hm : 0 < m := hcard ▸ Fintype.card_pos
  exact FinalBooleanVerifier.cnf_nonempty G vertices edges hm

/-- The checked final Boolean-verifier count bound produces exactly the
nonempty clause-gap premise of SourceGap, with denominator `40960 * b`. -/
theorem cnf_clauseGap [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (a b : ℕ) (hb : 0 < b)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      a * Fintype.card E ≤ b * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      ((a : ℚ) / ((b : ℚ) * 40960)) := by
  have h := clauseGap_of_count (FinalBooleanVerifier.cnf G vertices edges) a (b * 40960)
    (cnf_nonempty_of_nonempty_darts G vertices edges)
    (Nat.mul_pos hb (by decide)) (FinalBooleanVerifier.cnf_gap G vertices edges a b hgap)
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using h

/-- The unit-numerator gap supplied by the final powering stage has the
fixed rational clause gap `1 / (40960 * walkLength)`. -/
theorem cnf_clauseGap_unit [Fintype E] [Nonempty E]
    (G : ConstraintGraph V E FinalBooleanVerifier.Label)
    (vertices : V ≃ Fin n) (edges : E ≃ Fin m) (walkLength : ℕ)
    (hwalk : 0 < walkLength)
    (hgap : ∀ labeling : V → FinalBooleanVerifier.Label,
      Fintype.card E ≤ walkLength * G.rejectionCount labeling) :
    SourceGap.ClauseGap (FinalBooleanVerifier.cnf G vertices edges)
      (1 / (40960 * (walkLength : ℚ))) := by
  have h := cnf_clauseGap G vertices edges 1 walkLength hwalk
    (by simpa only [one_mul] using hgap)
  simpa only [Nat.cast_one, mul_comm] using h

end UniqueGamesTheorem.Foundations.Hastad.SourceNonempty


end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_FinalTableFormula
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.inputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_append _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_cons _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.outputStream_nil _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_done _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_length _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.remainingEvents_zero _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_accumulator _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_index _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_input _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFMachine.Program.rowResult_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_darts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_headValue _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_relation _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_reverseIndex _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_row _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_accepts _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_head _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_reverse _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_semantics_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableBits _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tableWords _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_tail _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.FinalCNFTableAdapter.genericTable_vertices _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.equalityRelation_apply _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.localStep_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_dummy _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingInternalRows.row_tail_original _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.actualRow_tail _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_dummy_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_relation _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PreprocessingRegularWords.inherited_original_reverse _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_darts _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RawInitialTables.table_vertices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! The exact table-to-formula converter used by the final CNF machine.
Its semantic count premise is explicit; amplification supplies that premise
elsewhere. The converter chooses no vertex or dart numbering. -/

namespace UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

open Target Complexity

/-- Boolean labels and numeric labels have exactly the same rejected darts. -/
theorem tableGraph_rejectionCount (table : GraphTables.Table)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    (FinalCNFPattern.tableGraph table).rejectionCount labeling =
      (GraphTables.semantics table).rejectionCount
        (fun v => FinalCNFPattern.labelEquiv (labeling v)) := by
  have h := (GraphTables.semantics table).reindex_rejectionCount
    (Equiv.refl _) (Equiv.refl _) FinalCNFPattern.labelEquiv.symm
    (fun v => FinalCNFPattern.labelEquiv (labeling v))
  simpa [FinalCNFPattern.tableGraph, ConstraintGraph.labelingEquiv] using h

/-- A uniform numeric-label count bound transfers to the machine's Boolean-label graph. -/
theorem tableGraph_count_lower (table : GraphTables.Table) (walkLength : Nat)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ walkLength * (GraphTables.semantics table).rejectionCount labeling)
    (labeling : Fin table.vertices → FinalBooleanVerifier.Label) :
    Fintype.card (Fin table.darts) ≤
      walkLength * (FinalCNFPattern.tableGraph table).rejectionCount labeling := by
  rw [Fintype.card_fin, tableGraph_rejectionCount]
  exact hgap _

theorem clauseGap (table : GraphTables.Table) (hd : 0 < table.darts)
    (hgap : ∀ labeling : Fin table.vertices → GraphTables.Label,
      table.darts ≤ FinalConstants.walkLength *
        (GraphTables.semantics table).rejectionCount labeling) :
    Hastad.SourceGap.ClauseGap (output table) PCPIteration.finalClauseGap := by
  let : Nonempty (Fin table.darts) := ⟨⟨0, hd⟩⟩
  exact Hastad.SourceNonempty.cnf_clauseGap_unit (FinalCNFPattern.tableGraph table)
    (Equiv.refl _) (Equiv.refl _) FinalConstants.walkLength
    FinalConstants.walkLength_positive (tableGraph_count_lower table _ hgap)

end UniqueGamesTheorem.Foundations.PCP.FinalTableFormula

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_PCP_TableGapReductionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.PCPSource.clauseCount_neZero _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


/-! Both semantic implications for the actual stored-table 3SAT gap map.
The positive clause gap follows from the full actual repeated transformation.
The full map admits a polynomial-time machine. -/

namespace UniqueGamesTheorem.Foundations.PCP.TableGapReduction

open RoundTables TableIteration SpectralReturn Target

variable (H : BaseTable)
  (certificate : SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))

include certificate

theorem output_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (labeling : Fin (outputTable H F).vertices → GraphTables.Label) :
    (outputTable H F).darts ≤ FinalConstants.walkLength *
      (GraphTables.semantics (outputTable H F)).rejectionCount labeling := by
  have hp := output_darts_positive H F
  let : Nonempty (Fin (outputTable H F).darts) := ⟨⟨0, hp⟩⟩
  have bound := output_gap H certificate F unsat
  change FinalConstants.cap ≤ (GraphTables.semantics (TableIteration.output H F).val).gap at bound
  rw [output_val] at bound
  have count := ((GraphTables.semantics (outputTable H F)).le_gap_iff FinalConstants.cap).mp bound labeling
  simp only [Fintype.card_fin] at count
  have ht : (0 : ℝ) < FinalConstants.walkLength := Nat.cast_pos.mpr FinalConstants.walkLength_positive
  have divided : ((outputTable H F).darts : ℝ) / FinalConstants.walkLength ≤
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) := by
    simpa only [FinalConstants.cap, one_div_mul_eq_div] using count
  have multiplied := (div_le_iff₀ ht).mp divided
  exact_mod_cast (show ((outputTable H F).darts : ℝ) ≤ (FinalConstants.walkLength : ℝ) *
      ((GraphTables.semantics (outputTable H F)).rejectionCount labeling : ℝ) by
    simpa only [mul_comm] using multiplied)

theorem gapMap_clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    Hastad.SourceGap.ClauseGap (gapMap H F) PCPIteration.finalClauseGap :=
  FinalTableFormula.clauseGap (outputTable H F) (output_darts_positive H F)
    (output_count_gap H certificate F unsat)

end UniqueGamesTheorem.Foundations.PCP.TableGapReduction



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PCPSource
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_extend _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.clause_eval_restrict _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_clause_count _root_.OAI.PerfectCompleteness.BinaryOccurrenceRename.renamed_variable_count _root_.OAI.PerfectCompleteness.NormalizedSourceInput.clause_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.fromReduction_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_bits _root_.OAI.PerfectCompleteness.NormalizedSourceInput.normalized_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.raw_formula _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.NormalizedSourceInput.variable_eq _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SourceClauseReaderMachine.clauseShape_eq _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.body_nil _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.recordWords_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.records_length _root_.OAI.PerfectCompleteness.SourceOccurrenceEncoding.words_length _root_.OAI.PerfectCompleteness.SourceTupleData.digits_at _root_.OAI.PerfectCompleteness.SourceTupleData.table_at _root_.OAI.PerfectCompleteness.SourceTupleData.variables_at _root_.OAI.PerfectCompleteness.SourceTupleData.work_at _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_clause_count _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.Circuit.toFormula_variables _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.CookLevin.gateClauses_length
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PCPSource

open UniqueGamesTheorem.Foundations Target PCP SourceClause
open scoped BigOperators

noncomputable section

theorem finalClauseGap_eq : PCPIteration.finalClauseGap = 1 / (baseDenominator : ℚ) := by
  simp only [PCPIteration.finalClauseGap, baseDenominator, Nat.cast_mul, Nat.cast_ofNat]

theorem rawFormula_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (A : Fin (rawFormula F).variables → Bool) :
    1 * (rawFormula F).clauses.length ≤
      baseDenominator * NameCompaction.failedCount (rawFormula F) A := by
  have hr := (TableGapReduction.gapMap_clauseGap baseTable baseTable_certificate F unsat).2 A
  have hr' : (PCPIteration.finalClauseGap : ℝ) * ((rawFormula F).clauses.length : ℝ) ≤
      (NameCompaction.failedCount (rawFormula F) A : ℝ) :=
    hr.trans_eq (congrArg (fun count : Nat => (count : ℝ))
      (NameCompaction.verifier_failureCount (rawFormula F) A))
  have hq : PCPIteration.finalClauseGap * ((rawFormula F).clauses.length : ℚ) ≤
      (NameCompaction.failedCount (rawFormula F) A : ℚ) := by
    exact_mod_cast hr'
  rw [finalClauseGap_eq, one_div_mul_eq_div] at hq
  have hden : (0 : ℚ) < baseDenominator := by exact_mod_cast baseDenominator_pos
  have h := (div_le_iff₀ hden).mp hq
  have hnat : (rawFormula F).clauses.length ≤
      baseDenominator * NameCompaction.failedCount (rawFormula F) A := by
    exact_mod_cast (show ((rawFormula F).clauses.length : ℚ) ≤
      (baseDenominator : ℚ) * (NameCompaction.failedCount (rawFormula F) A : ℚ) by
        simpa only [mul_comm] using h)
  simpa only [Nat.one_mul] using hnat

theorem normalizedFormula_count_gap (F : Formula) (unsat : ¬ F.Satisfiable)
    (A : Fin (normalizedFormula F).variables → Bool) :
    (normalizedFormula F).clauses.length ≤
      sourceDenominator * NameCompaction.failedCount (normalizedFormula F) A := by
  simpa only [normalizedFormula, sourceDenominator, Nat.one_mul] using
    Normalization.normalize_gap (rawFormula F) 1 baseDenominator
      (rawFormula_count_gap F unsat) A

theorem failedCount_eq_fin_sum (F : Formula) (A : Fin F.variables → Bool) :
    NameCompaction.failedCount F A =
      ∑ i : Fin F.clauses.length, if (clauseAt F i).eval A then 0 else 1 := by
  unfold NameCompaction.failedCount
  rw [← NameCompaction.evaluations_allIndices, VerifierToCNF.count_false_map_sum]
  simp [allIndices, List.finRange, List.map_ofFn, List.sum_ofFn]

theorem violatedCount_eq_failedCount (F : Formula)
    (A : Fin (normalizedFormula F).variables → Bool) :
    SourceGame.violatedCount (clauseFamily F) A =
      NameCompaction.failedCount (normalizedFormula F) A := by
  rw [failedCount_eq_fin_sum]
  rfl

theorem clauseGap (F : Formula) (unsat : ¬ F.Satisfiable) :
    SourceAmplification.ClauseGap (clauseFamily F) sourceGap := by
  intro A
  have hnat := normalizedFormula_count_gap F unsat A
  have hq : ((normalizedFormula F).clauses.length : ℚ) ≤
      (sourceDenominator : ℚ) * (NameCompaction.failedCount (normalizedFormula F) A : ℚ) := by
    exact_mod_cast hnat
  rw [← violatedCount_eq_failedCount] at hq
  change (1 / (sourceDenominator : ℚ)) * ((normalizedFormula F).clauses.length : ℚ) ≤ _
  rw [one_div_mul_eq_div]
  have hden : (0 : ℚ) < sourceDenominator := by exact_mod_cast sourceDenominator_pos
  exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hq)

end
end PerfectCompleteness.PCPSource

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_PreprocessingMachineLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.PCPSourceMachine

open Turing UniqueGamesTheorem.Foundations Complexity Target

noncomputable section

theorem rawSource_clauseGap (input : List Bool) (unsat : ¬BinaryLanguage.language input) :
    SourceAmplification.ClauseGap (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
      PCPSource.sourceGap :=
  PCPSource.clauseGap (BinaryLanguage.totalRename input)
    (fun sat => unsat ((BinaryLanguage.totalRename_satisfiable_iff input).mp sat))

end
end PerfectCompleteness.PCPSourceMachine

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatent
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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


end
end PerfectCompleteness.UniformLatent

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OddListExtraction.form_atom_self _root_.OAI.PerfectCompleteness.OddListExtraction.multiplicationForm_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ChildBlockCardinality

theorem shape_bound_pos (branch : Nat → Nat) (n t calls : Nat) (rows : Nat → Nat) :
    0 < bound branch n t calls rows :=
  bound_pos calls rows (fun _ _ => MixedSupport.Slot.bit 0)


open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t calls : Nat} {rows : Nat → Nat}
    {slots : Slots branch n → Fin t → MixedSupport.Slot}

theorem allZero_iff (x : Raw calls rows slots) :
    allZero x = true ↔ x = zeroRaw calls rows slots := by
  classical
  simp only [allZero, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, ha⟩
    apply Prod.ext
    · funext q
      exact hc q
    · funext node row
      exact ha node row
  · intro h
    subst x
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩

theorem probability_allZero :
    (FiniteDistribution.uniform (Raw calls rows slots)).probability allZero =
      1 / (Fintype.card (Raw calls rows slots) : ℝ) := by
  classical
  have hevent : (allZero : Raw calls rows slots → Bool) =
      fun x => decide (x = zeroRaw calls rows slots) := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [allZero_iff, decide_eq_true_eq]
  rw [hevent]
  simp only [FiniteDistribution.probability, FiniteDistribution.uniform,
    decide_eq_true_eq, one_div]
  rw [Finset.sum_eq_single (zeroRaw calls rows slots)]
  · simp
  · intro x _ hx
    exact ite_eq_right hx
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

theorem cleanLowerBound_le_probability :
    cleanLowerBound branch n t calls rows ≤
      (FiniteDistribution.uniform (Raw calls rows slots)).probability allZero := by
  rw [probability_allZero]
  exact one_div_le_one_div_of_le (Nat.cast_pos.mpr Fintype.card_pos)
    (by exact_mod_cast fintype_card_le calls rows slots)

end
end PerfectCompleteness.ChildBlockCardinality


namespace PerfectCompleteness.FixedSourceBranching

open FixedRows AscendingBranching ChildBlockCardinality

noncomputable section

variable {δ : ℚ} (plan : Plan δ) (hδ : 0 < δ)

theorem source_rate (cost : Nat) (hcost : 0 < cost)
    (hbudget : SourceOddLists.alphabetLog (cutoff plan hδ) (sourceLength plan hδ) ≤ cost)
    (input : List Bool) (unsat : ¬BinaryLanguage.language input) (k : Nat) :
    ((SourceOddLists.game (cutoff plan hδ)
      (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
      (sourceLength plan hδ)).repetition k).value ≤
      (RepetitionRate.halfRate cost : ℝ) ^ k :=
  SourceOddLists.repetition_halfRate
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) PCPSource.sourceGap
    PCPSource.sourceGap_pos PCPSource.sourceGap_le_one
    (PCPSourceMachine.rawSource_clauseGap input unsat) hcost hbudget k

end
end PerfectCompleteness.FixedSourceBranching

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedCardinality
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedCardinality

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces PointwiseSpaces UniformLatent

variable {branch : Nat → Nat} {n t : Nat}

theorem factor_card_eq (square : Bool)
    (ids ids' : RecursiveSpaces.Slots branch n → Fin t → Nat) :
    Fintype.card (Factor square ids) = Fintype.card (Factor square ids') :=
  Fintype.card_congr (factorEquiv square ids ids')

section Sampler

variable {S J D : Type*} [Fintype S] [Fintype J] [DecidableEq J] [Fintype D]
  (branch : Nat → Nat) (t : Nat) (height : J → Nat) (square : J → Bool)

omit [Fintype J] [DecidableEq J] in
theorem shapeCardinality_pos (j : J) : 0 < shapeCardinality branch t height square j :=
  Fintype.card_pos

variable (ids : (s : S) → (j : J) → RecursiveSpaces.Slots branch (height j) → Fin t → Nat)

omit [DecidableEq J] in
theorem shape_zero_probability_pos :
    0 < (∏ j, 1 / (shapeCardinality branch t height square j : ℝ)) := by
  apply Finset.prod_pos
  intro j _
  exact one_div_pos.mpr (Nat.cast_pos.mpr (shapeCardinality_pos branch t height square j))

end Sampler

end PerfectCompleteness.ProjectedCardinality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanTreeFactors
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanTreeFactors

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays
open ProjectedCardinality FiniteProduct CleanConditioning

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem rawLaw_uniform (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    rawLaw calls rows ids = FiniteDistribution.uniform (Raw calls rows ids) := by
  unfold rawLaw
  rw [UniformLinearImage.law_uniform, FiniteDistribution.pushforward_equiv]
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change 1 / (Fintype.card ((j : Index branch n calls rows) → Factors calls rows ids j) : ℝ) =
    1 / (Fintype.card (Raw calls rows ids) : ℝ)
  rw [Fintype.card_congr (rawEquiv calls rows ids)]

theorem allZero_rawEquiv (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat)
    (x : (j : Index branch n calls rows) → Factors calls rows ids j) :
    allZero calls rows ids (rawEquiv calls rows ids x) =
      allEvent (fun j y => decide (y = factorZero
        (square calls rows j) (factorIds calls rows ids j))) x := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [allZero, allEvent, decide_eq_true_eq]
  constructor
  · rintro ⟨hc, ha⟩ j
    cases j with
    | inl q => exact hc q
    | inr p => exact ha p.1 p.2
  · intro h
    exact ⟨fun q => h (.inl q), fun node row => h (.inr ⟨node, row⟩)⟩

theorem probability_allZero (calls : Nat) (rows : Nat → Nat)
    (ids : Slots branch n → Fin t → Nat) :
    (rawLaw calls rows ids).probability (allZero calls rows ids) =
      ∏ j : Index branch n calls rows,
        1 / (shapeCardinality branch t (height calls rows) (square calls rows) j : ℝ) := by
  rw [rawLaw, FiniteDistribution.probability_pushforward]
  simp_rw [allZero_rawEquiv]
  rw [probability_law_all]
  apply Finset.prod_congr rfl
  intro j _
  rw [UniformLatent.probability_uniform_singleton]
  rw [factor_card_eq (square calls rows j) (factorIds calls rows ids j) (fun _ _ => 0)]
  rfl

end
end PerfectCompleteness.CleanTreeFactors

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutCallsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.WholeCutCalls

open RecursiveSpaces DescendantSpaces TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m : Nat}

theorem card_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) :
    Fintype.card (Index rows repeats (.step i p)) =
      (2 ^ rows (n + 1) - 1) * Fintype.card (TerminalIndex repeats (.step i p)) +
        Fintype.card (Index rows repeats p) := by
  change Fintype.card
    ((BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p)) ⊕
      Index rows repeats p) = _
  rw [Fintype.card_sum, Fintype.card_prod, direction_card]

theorem card_eq_formula (rows repeats : Nat → Nat) (p : Path branch n m) :
    Fintype.card (Index rows repeats p) = rows m +
      ∑ h ∈ Finset.Ioc m n, (2 ^ rows h - 1) *
        ∏ k ∈ Finset.Ioc m h, 2 * repeats k := by
  induction p with
  | refl m => simp only [card_refl, Finset.Ioc_self, Finset.sum_empty, Nat.add_zero]
  | @step n m i p ih =>
      rw [card_step, TerminalCalls.card_eq_prod, ih,
        Finset.sum_Ioc_succ_top p.height_le]
      omega

end
end PerfectCompleteness.WholeCutCalls



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CutChildCleanLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.ProjectedCleanRate

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces ProjectedCardinality CleanTreeFactors UniformCleanSources

noncomputable section

theorem zeroProbability_positive (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) : 0 < zeroProbability branch height t calls rows :=
  shape_zero_probability_pos branch t
    (CleanTreeFactors.height calls rows) (CleanTreeFactors.square calls rows)

theorem zeroProbability_le_one (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) : zeroProbability branch height t calls rows ≤ 1 := by
  change (∏ j : CleanTreeFactors.Index branch height calls rows,
    1 / (shapeCardinality branch t
      (CleanTreeFactors.height calls rows) (CleanTreeFactors.square calls rows) j : ℝ)) ≤ 1
  rw [← CleanTreeFactors.probability_allZero calls rows
    (fun (_ : Slots branch height) (_ : Fin t) => 0)]
  exact FiniteDistribution.probability_le_one _ _

theorem raw_zero_probability (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) (ids : Slots branch height → Fin t → Nat) :
    (CleanTreeFactors.rawLaw calls rows ids).probability
      (CleanTreeFactors.allZero calls rows ids) =
        zeroProbability branch height t calls rows :=
  CleanTreeFactors.probability_allZero calls rows ids

theorem coefficient_bounds {L : Nat} (hL : 0 < L) (branch : Nat → Nat)
    (height t calls : Nat) (rows : Nat → Nat) :
    0 < coefficient L branch height t calls rows ∧
      coefficient L branch height t calls rows ≤ 1 := by
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : (0 : ℝ) < 48000 * L := by positivity
  have hp := zeroProbability_positive branch height t calls rows
  have hp1 := zeroProbability_le_one branch height t calls rows
  constructor
  · exact div_pos hp hden
  · apply (div_le_one hden).2
    linarith

end
end PerfectCompleteness.ProjectedCleanRate

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderSeedLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderSeedLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays CleanDecoderContext
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (E : Exposed branch rows repeats n h t v m upper d)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : CleanLeftDecoder.Useful (leftExposed E) upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (lower E)) (threshold : ℝ)

attribute [local instance] OAI.PerfectCompleteness.CleanDecoderSeedLaw.leftOwnFintype
attribute [local instance] OAI.PerfectCompleteness.CleanDecoderSeedLaw.rightOwnFintype
attribute [local instance] OAI.PerfectCompleteness.CleanDecoderSeedLaw.leftAnswerFintype
attribute [local instance] OAI.PerfectCompleteness.CleanDecoderSeedLaw.rightAnswerFintype
theorem read_law (left : LeftOwn E) (right : RightOwn E) :
    (seedLaw E σ useful r ρ A W a threshold).pushforward
        (fun seed => (seed.1 left, seed.2 right)) =
      (leftKernel E σ useful r ρ A left).product
        (rightKernel E σ W a threshold right) :=
  DependentDecoderSampling.read_law
    (leftKernel E σ useful r ρ A) (rightKernel E σ W a threshold) left right

theorem probability_read (left : LeftOwn E) (right : RightOwn E)
    (event : LeftAnswer E left → RightAnswer E right → Bool) :
    (seedLaw E σ useful r ρ A W a threshold).probability
        (fun seed => event (seed.1 left) (seed.2 right)) =
      ((leftKernel E σ useful r ρ A left).product
        (rightKernel E σ W a threshold right)).probability
          (fun answer => event answer.1 answer.2) := by
  have hread := FiniteDistribution.probability_pushforward
    (seedLaw E σ useful r ρ A W a threshold)
    (fun seed : Seed E => (seed.1 left, seed.2 right))
    (fun answer => event answer.1 answer.2)
  rw [read_law] at hread
  exact hread.symm

end
end PerfectCompleteness.CleanDecoderSeedLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderRateLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderPairLaw

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (record : CleanDecoderRate.Record S) →
    CleanLeftDecoder.Useful (CleanDecoderContext.leftExposed (CleanDecoderRate.context S record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

theorem probability_read (cube : Nat) (hcube : 0 < cube)
    (event : (x : CleanDecoderRate.Sample S) → Pair S x → Bool) :
    (pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => event z.1 z.2) =
    (CleanDecoderRate.law S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => event z.1 (read S z.1 z.2)) := by
  rw [pairLaw, CleanDecoderRate.law, RecordSeedSampling.freshLaw,
    CompletionSoundness.sigmaLaw_probability, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro x
  exact (CleanDecoderSeedLaw.probability_read (context S x) σ
    (useful (CleanDecoderRate.observations S x)) r ρ A W a threshold
    (leftOwn S x) (rightOwn S x) (fun left right => event x (left, right))).symm

variable (hbranch : ∀ k < n, 0 < branch k)

theorem pair_probability_eq (s cube : Nat) (hcube : 0 < cube) :
    (pairLaw S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => pairAgrees S hbranch s z.1 z.2) =
    (CleanDecoderRate.law S σ useful r ρ A W a threshold cube hcube).probability
      (fun z => CleanDecoderRate.agrees S hbranch s z.1 z.2) := by
  exact probability_read S σ useful r ρ A W a threshold cube hcube (pairAgrees S hbranch s)

end
end PerfectCompleteness.CleanDecoderPairLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedCallBudgetLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedCallBudget

open RecursiveSpaces DescendantSpaces
open scoped BigOperators

noncomputable section

theorem pairCount_le {depth root cutoff : Nat} (rows repeats : Nat → Nat)
    (hroot : root ≤ depth) (hcutoff : cutoff ≤ depth) :
    pairCount rows repeats root cutoff ≤ budget depth rows repeats := by
  let a : Fin (depth + 1) := ⟨root, Nat.lt_succ_of_le hroot⟩
  let b : Fin (depth + 1) := ⟨cutoff, Nat.lt_succ_of_le hcutoff⟩
  have hinner : pairCount rows repeats root cutoff ≤
      ∑ j : Fin (depth + 1), pairCount rows repeats a.val j.val :=
    Finset.single_le_sum (fun j _ => Nat.zero_le
      (pairCount rows repeats a.val j.val)) (Finset.mem_univ b)
  have houter : (∑ j : Fin (depth + 1), pairCount rows repeats a.val j.val) ≤
      ∑ i : Fin (depth + 1), ∑ j : Fin (depth + 1),
        pairCount rows repeats i.val j.val :=
    Finset.single_le_sum (fun i _ => Nat.zero_le
      (∑ j : Fin (depth + 1), pairCount rows repeats i.val j.val))
      (Finset.mem_univ a)
  unfold budget
  omega

theorem modified_calls_le {depth root cutoff : Nat} {branch : Nat → Nat}
    (rows repeats : Nat → Nat) (p : Path branch root cutoff)
    (hroot : root ≤ depth) :
    Fintype.card (WholeCutCalls.Index rows repeats p) ≤ budget depth rows repeats := by
  rw [WholeCutCalls.card_eq_formula]
  have h := pairCount_le rows repeats hroot (p.height_le.trans hroot)
  unfold pairCount OriginalCutCalls.count at h
  omega

theorem child_bound_mono {calls calls' : Nat} (hcalls : calls ≤ calls')
    (branch : Nat → Nat) (height sourceLength : Nat) (rows : Nat → Nat) :
    ChildBlockCardinality.bound branch height sourceLength calls rows ≤
      ChildBlockCardinality.bound branch height sourceLength calls' rows := by
  apply Nat.mul_le_mul_right
  apply pow_le_pow_right₀ _ hcalls
  unfold TreeCardinality.functionBound
  exact one_le_pow₀ (by decide : (1 : Nat) ≤ 2)

end
end PerfectCompleteness.FixedCallBudget


namespace PerfectCompleteness.FixedParameters

open FixedRows AscendingBranching

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem source_rate (input : List Bool) (unsat : ¬BinaryLanguage.language input)
    (k : Nat) :
    ((SourceOddLists.game (cutoff p.plan hδ)
      (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
      (sourceLength p.plan hδ)).repetition k).value ≤
      (RepetitionRate.halfRate p.alphabetCost : ℝ) ^ k :=
  FixedSourceBranching.source_rate p.plan hδ p.alphabetCost
    p.alphabetCost_pos p.alphabetCost_bound input unsat k

end
end PerfectCompleteness.FixedParameters

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_FixedCleanRate
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedCleanRate

open ChildBlockCardinality ProjectedCleanRate

noncomputable section

theorem zeroProbability_lower (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) :
    1 / (bound branch height t calls rows : ℝ) ≤
      zeroProbability branch height t calls rows := by
  let ids : RecursiveSpaces.Slots branch height → Fin t → Nat := fun _ _ => 0
  rw [← raw_zero_probability branch height t calls rows ids,
    CleanTreeFactors.rawLaw_uniform]
  exact cleanLowerBound_le_probability
    (slots := ProjectedCardinality.projectedSlots ids)

theorem conservative_coefficient_le {calls budget cost : Nat}
    (hcalls : calls ≤ budget) (hcost : 0 < cost)
    (branch : Nat → Nat) (height t : Nat) (rows : Nat → Nat) :
    FixedBranching.cleanRate cost (bound branch height t budget rows : ℝ) ≤
      coefficient cost branch height t calls rows := by
  have hbound : (bound branch height t calls rows : ℝ) ≤
      (bound branch height t budget rows : ℝ) := by
    exact_mod_cast FixedCallBudget.child_bound_mono hcalls branch height t rows
  have hpositive : (0 : ℝ) < bound branch height t calls rows :=
    Nat.cast_pos.mpr (shape_bound_pos branch height t calls rows)
  have hzero : 1 / (bound branch height t budget rows : ℝ) ≤
      zeroProbability branch height t calls rows :=
    (one_div_le_one_div_of_le hpositive hbound).trans
      (zeroProbability_lower branch height t calls rows)
  have hden : (0 : ℝ) < 48000 * cost := by
    have : (0 : ℝ) < cost := by exact_mod_cast hcost
    positivity
  calc
    _ = (1 / (bound branch height t budget rows : ℝ)) / (48000 * cost) := by
      unfold FixedBranching.cleanRate
      ring
    _ ≤ _ := div_le_div_of_nonneg_right hzero hden.le

theorem decay_le_conservative {calls budget cost cube : Nat}
    (hcalls : calls ≤ budget) (hcost : 0 < cost) (hcube : 2 ≤ cube)
    (branch : Nat → Nat) (height t : Nat) (rows : Nat → Nat) :
    (1 - coefficient cost branch height t calls rows / (cube : ℝ) ^ 2) ^ (cube ^ 3) ≤
      (1 - FixedBranching.cleanRate cost
        (bound branch height t budget rows : ℝ) / (cube : ℝ) ^ 2) ^ (cube ^ 3) := by
  have hc : (2 : ℝ) ≤ cube := by exact_mod_cast hcube
  have hsquare : (1 : ℝ) ≤ (cube : ℝ) ^ 2 := by nlinarith
  have hden : (0 : ℝ) < (cube : ℝ) ^ 2 := by positivity
  have hcoef := (coefficient_bounds hcost branch height t calls rows).2
  have hbase : 0 ≤ 1 - coefficient cost branch height t calls rows / (cube : ℝ) ^ 2 := by
    have := (div_le_one hden).mpr (hcoef.trans hsquare)
    linarith
  apply pow_le_pow_left₀ hbase
  have h := div_le_div_of_nonneg_right
    (conservative_coefficient_le hcalls hcost branch height t rows) hden.le
  linarith

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

theorem actual_clean_error {calls : Nat} (hcalls : calls ≤ FixedParameters.calls p.plan)
    (height : Nat) :
    (1 - coefficient p.alphabetCost (FixedParameters.branch p) height
      (FixedRows.sourceLength p.plan hδ) calls (FixedRows.rows p.plan) /
        (p.cubeSize height : ℝ) ^ 2) ^ (p.cubeSize height ^ 3) < p.accuracy := by
  have hdecay := decay_le_conservative hcalls p.alphabetCost_pos
    (p.cube_errors height).1 (FixedParameters.branch p) height
    (FixedRows.sourceLength p.plan hδ) (FixedRows.rows p.plan)
  exact hdecay.trans_lt (p.cube_errors height).2.2.2.2

end
end PerfectCompleteness.FixedCleanRate

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedDecoderCleanRateLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedDecoderCleanRate

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {n h : Nat} {upper : Nodes (FixedParameters.branch p) n}
  {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (G : Geometry p n h upper d)

theorem calls_le (input : List Bool) (hn : n ≤ p.plan.depth) :
    Fintype.card (CleanDecoderRate.Calls (setup p G input)) ≤ FixedParameters.calls p.plan := by
  have hactual := FixedCallBudget.modified_calls_le (FixedRows.rows p.plan)
    (FixedRows.repeats p.plan) (CleanDecoderRate.path (setup p G input)) hn
  apply hactual.trans
  unfold FixedParameters.calls
  omega

variable (input : List Bool)
  (σ : KeyStrategy.Strategy
    (TreeCanonical.locationCount (FixedParameters.branch p) n
      (FixedRows.sourceLength p.plan hδ)))
  (useful : (record : CleanDecoderRate.Record (setup p G input)) →
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed (CleanDecoderRate.context (setup p G input) record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block (FixedRows.rows p.plan) upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector (FixedRows.rows p.plan) upper))
  (a : OwnInputReference.LowerVector (FixedRows.rows p.plan)
    (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

theorem probability_lt_accuracy (unsat : ¬ BinaryLanguage.language input)
    (hn : n ≤ p.plan.depth) (hρ : 0 < ρ) :
    (CleanDecoderRate.law (setup p G input) σ useful r ρ A W a threshold
      (p.cubeSize h) (cubePositive p h)).probability
        (fun z => CleanDecoderRate.agrees (setup p G input) (branchPositive p)
          (FixedRows.cutoff p.plan hδ) z.1 z.2) < p.accuracy := by
  have hbound := CleanDecoderRate.bound (setup p G input) σ useful r ρ A W a threshold
    (branchPositive p) (cubePositive p h) hρ (FixedParameters.source_rate p input unsat)
  apply hbound.trans_lt
  simpa only [FixedParameters.branch] using
    FixedCleanRate.actual_clean_error p (calls_le p G input hn) h

end
end PerfectCompleteness.FixedDecoderCleanRate

end

section

namespace PerfectCompleteness.FixedDecoderPairRate

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays FixedDecoderCleanRate

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)
  {n h : Nat} {upper : Nodes (FixedParameters.branch p) n}
  {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (G : Geometry p n h upper d)
  (input : List Bool)
  (σ : KeyStrategy.Strategy
    (TreeCanonical.locationCount (FixedParameters.branch p) n
      (FixedRows.sourceLength p.plan hδ)))
  (useful : (record : CleanDecoderRate.Record (setup p G input)) →
    CleanLeftDecoder.Useful
      (CleanDecoderContext.leftExposed (CleanDecoderRate.context (setup p G input) record))
      upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block (FixedRows.rows p.plan) upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector (FixedRows.rows p.plan) upper))
  (a : OwnInputReference.LowerVector (FixedRows.rows p.plan)
    (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

theorem probability_lt_accuracy_oai (unsat : ¬ BinaryLanguage.language input)
    (hn : n ≤ p.plan.depth) (hρ : 0 < ρ) :
    (CleanDecoderPairLaw.pairLaw (setup p G input) σ useful r ρ A W a threshold
      (p.cubeSize h) (cubePositive p h)).probability
        (fun z => CleanDecoderPairLaw.pairAgrees (setup p G input) (branchPositive p)
          (FixedRows.cutoff p.plan hδ) z.1 z.2) < p.accuracy := by
  rw [CleanDecoderPairLaw.pair_probability_eq]
  exact FixedDecoderCleanRate.probability_lt_accuracy p G input σ useful r ρ A W a threshold
    unsat hn hρ

end
end PerfectCompleteness.FixedDecoderPairRate

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedDecoderPairRate.probability_lt_accuracy_oai := @OAI.PerfectCompleteness.FixedDecoderPairRate.probability_lt_accuracy_oai
