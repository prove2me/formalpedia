-- Prove2me | solution 1 for OAI.PerfectCompleteness.StoppedProjectedUsefulProbability.original_probability_eq_usefulProbability
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:27:06.290041+00:00
-- url     : https://prove2.me/submissions/882c18f4-1823-480a-8b2d-59e4ac661b87

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
import Theorems.Thm_OAI_PerfectCompleteness_StoppedProjectedUsefulAverage_original_probability_eq_mean
import Theorems.Thm_OAI_PerfectCompleteness_StoppedUsefulPairLaw_observe_law

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_HiddenBucketBias
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HiddenBucketBias

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators TensorProduct Classical

noncomputable section

variable {ℓ : Nat} {Ω H : Type*} [Fintype Ω]
  [AddCommGroup H] [Module F2 H]

theorem product_fst {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    (μ.product ν).pushforward Prod.fst = μ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  calc
    _ = (μ.product ν).expectation (fun x => if x.1 = a then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
    _ = μ.expectation (fun x => ν.expectation (fun _ => if x = a then 1 else 0)) :=
      FiniteDistribution.expectation_product μ ν _
    _ = _ := by simp [FiniteDistribution.expectation, mul_ite, ν.normalized]

end

end PerfectCompleteness.HiddenBucketBias

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_PreliminaryAveraging
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PreliminaryAveraging

open PreliminarySampler TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

theorem probability_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (event : X × Y → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun x => ν.probability (fun y => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

end
end PerfectCompleteness.PreliminaryAveraging

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_StoppedProjectedBuckets
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedBuckets

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
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

variable (hbranch : ∀ k < j + 1, 0 < branch k)
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedBuckets.backgroundFintype
attribute [local instance] OAI.PerfectCompleteness.StoppedProjectedBuckets.rowSpaceFintype
theorem usefulProbability_eq_mean (κ : ℝ) :
    usefulProbability clauses rows repeats hupper hij designated hrows o hbranch flag σ κ =
      (StoppedProjectedBucketIndex.baseLaw (t := t) hij hbranch flag).expectation (fun base =>
        HierarchicalAdviceFromBuckets.usefulProbability
          (experiment clauses rows repeats hupper hij designated hrows o hbranch flag σ) κ
          (exteriorLaw clauses rows repeats hupper hij designated hrows o base)
          (fun external => background clauses rows repeats hupper hij designated hrows o
            ⟨base, external⟩)
          (fun external => scalarLaw clauses rows repeats hupper hij designated hrows o
            ⟨base, external⟩)
          (rows_positive rows hupper hrows o)) := by
  simp only [usefulProbability, HierarchicalAdviceFromBuckets.usefulProbability,
    HierarchicalUsefulCollision.law, CompletionSoundness.sigmaLaw_probability,
    externalLaw, CandidateCoupling.expectation_sigmaLaw,
    HierarchicalUsefulCollision.usefulEvent]

end
end PerfectCompleteness.StoppedProjectedBuckets

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedBucketUsefulProbability
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedBucketUsefulProbability

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

private theorem probability_product_fst {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A → Bool) :
    (μ.product ν).probability (fun z => event z.1) = μ.probability event := by
  have h := FiniteDistribution.probability_pushforward (μ.product ν) Prod.fst event
  rw [HiddenBucketBias.product_fst] at h
  exact h.symm

variable {branch : Nat → Nat} {N j i t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
  (chosen : Fin (branch j)) (q : Path branch j i)
  (native right : Slots branch N → Fin t → MixedSupport.Slot)
  (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))

variable (hrows : 0 < rows (j + 1)) (lowerLevel : Nat) {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays native rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch N t))

local instance rowSpaceFintype_r82aa54_1 : Fintype (NodeEmbedding.RowSpace native (upperNode p)) :=
  Fintype.ofFinite _
local instance backgroundFintype_r82aa54_1 :
    Fintype (HierarchicalMatrixTable.Background (rows := rows) native (upperNode p)) :=
  Fintype.ofFinite _
theorem usefulEvent_observe
    (sample : StoppedUsefulPairLaw.Sample rows repeats p chosen q right) :
    HierarchicalUsefulCollision.usefulEvent native (upperNode p) lowerLevel
        original arrays lowerEvent κ σ
        (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection)
        (StoppedUsefulPairLaw.observe rows repeats p chosen q native right projection sample) =
      HierarchicalUsefulCollision.usefulAccepted native (upperNode p) lowerLevel
        original arrays lowerEvent κ σ
        (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection
          (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection sample.2.1).1)
        (CutNodeRows.directionEquiv rows p sample.1)
        (CutNodeRows.bucketTapeEquiv rows p native
          (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection sample.2.1).2) :=
  rfl

theorem useful_probability_eq :
    (HierarchicalUsefulCollision.law native (upperNode p)
      (StoppedUsefulPairLaw.externalLaw rows repeats p chosen q right)
      (StoppedUsefulPairLaw.scalarLaw rows repeats p chosen q native right projection)
      (by simpa only [upperNode_height] using hrows)).probability
        (HierarchicalUsefulCollision.usefulEvent native (upperNode p) lowerLevel
          original arrays lowerEvent κ σ
          (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection)) =
      (StoppedUsefulPairLaw.directionLaw rows j hrows).expectation (fun a =>
        (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right).probability
          (fun tape => HierarchicalUsefulCollision.usefulAccepted native (upperNode p) lowerLevel
            original arrays lowerEvent κ σ
            (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection
              (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection tape).1)
            (CutNodeRows.directionEquiv rows p a)
            (CutNodeRows.bucketTapeEquiv rows p native
              (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection tape).2))) := by
  rw [← StoppedUsefulPairLaw.observe_law rows repeats p chosen q native right projection hrows,
    FiniteDistribution.probability_pushforward]
  simp_rw [usefulEvent_observe]
  rw [StoppedUsefulPairLaw.actualLaw, PreliminaryAveraging.probability_product]
  apply FiniteDistribution.expectation_congr
  intro a
  exact probability_product_fst
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right)
    (RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p right)))
    (fun tape => HierarchicalUsefulCollision.usefulAccepted native (upperNode p) lowerLevel
      original arrays lowerEvent κ σ
      (StoppedUsefulPairLaw.background rows repeats p chosen q native right projection
        (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection tape).1)
      (CutNodeRows.directionEquiv rows p a)
      (CutNodeRows.bucketTapeEquiv rows p native
        (StoppedUsefulPairLaw.readout rows repeats p chosen q native right projection tape).2))

end
end PerfectCompleteness.StoppedBucketUsefulProbability

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedProjectedUsefulProbability
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedUsefulProbability

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
  (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (κ : ℝ)

local notation "S" => StoppedProjectedExperiment.experiment clauses rows repeats hupper hij
  designated hbranch hrows flag σ

variable (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local instance nativeRowSpaceFintype_r82aa54_1 :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) := Fintype.ofFinite _
theorem stepTape_law
    (base : StoppedProjectedBucketIndex.Base (branch := branch) (i := i) (j := j) (t := t)) :
    (StoppedProjectedBucketIndex.tapeLaw clauses rows repeats hupper hij designated hrows o base).pushforward
      (fun tape => StoppedProjectedUsefulEvent.stepTape clauses rows repeats hupper hij designated o
        ⟨StoppedProjectedBucketIndex.key (n := n) rows hrows base, tape⟩) =
      WholeArraySampler.tapeLaw rows repeats
        ((StoppedProjectedExperiment.upperPath hupper o).append
          (.step (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
            (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)))
        (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base) :=
  StoppedOwnInputGeometry.pathTapeEquiv_law rows repeats
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
    (congrArg (fun p : Path branch n (i + 1) =>
      (⟨i + 1, p⟩ : Σ height, Path branch n height))
      (StoppedProjectedUsefulEvent.stepPath_eq rows hupper hij o
        (StoppedProjectedBucketIndex.key (n := n) rows hrows base)))

theorem directionLaw_eq :
    CanonicalDirections.levelLaw rows hrows (StoppedProjectedUsefulEvent.upperLevel hupper) =
      StoppedUsefulPairLaw.directionLaw rows j (hrows j) := rfl

theorem mean_eq_usefulProbability :
    StoppedProjectedUsefulAverage.mean clauses rows repeats hupper hij designated
      hbranch hrows flag σ κ o =
      StoppedProjectedBuckets.usefulProbability clauses rows repeats hupper hij designated
        hrows o hbranch flag σ κ := by
  rw [StoppedProjectedBuckets.usefulProbability_eq_mean]
  unfold StoppedProjectedUsefulAverage.mean
  apply FiniteDistribution.expectation_congr
  intro base
  have hfixed := StoppedBucketUsefulProbability.useful_probability_eq rows repeats
    (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
    (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
    (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base)
    (hrows j) (i + 1) (S o).original (S o).arrays
    (HierarchicalAdviceExperiment.lowerEvent (S o)) κ σ
  change _ = (HierarchicalUsefulCollision.law
    (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
    (StoppedProjectedBuckets.exteriorLaw clauses rows repeats hupper hij designated hrows o base)
    (fun external => StoppedProjectedBuckets.scalarLaw clauses rows repeats hupper hij designated
      hrows o ⟨base, external⟩) (StoppedProjectedBuckets.rows_positive rows hupper hrows o)).probability
      (HierarchicalUsefulCollision.usefulEvent
        (StoppedProjectedExperiment.nativeSlots clauses o) (StoppedProjectedExperiment.upper hupper o)
        (i + 1) (S o).original (S o).arrays (HierarchicalAdviceExperiment.lowerEvent (S o)) κ σ
        (fun external => StoppedProjectedBuckets.background clauses rows repeats hupper hij designated
          hrows o ⟨base, external⟩))
  refine Eq.trans ?_ hfixed.symm
  rw [directionLaw_eq rows hupper hrows]
  apply FiniteDistribution.expectation_congr
  intro direction
  rw [← stepTape_law clauses rows repeats hupper hij designated hrows o base]
  let event (tape : WholeArraySampler.Tape rows repeats
      ((StoppedProjectedExperiment.upperPath hupper o).append
        (.step (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
          (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)))
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)) : Bool :=
    let readout := StoppedUsefulPairLaw.readout rows repeats
      (StoppedProjectedExperiment.upperPath hupper o)
      (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
      (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
      (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base) tape
    HierarchicalUsefulCollision.usefulAccepted
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (WholeArrayInteriorExterior.upperNode (StoppedProjectedExperiment.upperPath hupper o))
      (i + 1) (S o).original (S o).arrays (HierarchicalAdviceExperiment.lowerEvent (S o)) κ σ
      (StoppedUsefulPairLaw.background rows repeats
        (StoppedProjectedExperiment.upperPath hupper o)
        (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
        (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)
        (StoppedProjectedExperiment.nativeSlots clauses o)
        (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base)
        (StoppedProjectedBuckets.projection clauses rows hupper hij designated hrows o base)
        readout.1)
      (CutNodeRows.directionEquiv rows (StoppedProjectedExperiment.upperPath hupper o) direction)
      (CutNodeRows.bucketTapeEquiv rows (StoppedProjectedExperiment.upperPath hupper o)
        (StoppedProjectedExperiment.nativeSlots clauses o) readout.2)
  have hp := FiniteDistribution.probability_pushforward
    (Ω := StoppedProjectedBucketIndex.Tape clauses rows repeats hupper hij designated hrows o base)
    (Γ := WholeArraySampler.Tape rows repeats
      ((StoppedProjectedExperiment.upperPath hupper o).append
        (.step (StoppedProjectedBuckets.chosen (n := n) rows hij hrows base)
          (StoppedProjectedBuckets.continuation (n := n) rows hij hrows base)))
      (StoppedProjectedBuckets.projected clauses rows hupper hij designated hrows o base))
    (StoppedProjectedBucketIndex.tapeLaw clauses rows repeats hupper hij designated hrows o base)
    (fun tape => StoppedProjectedUsefulEvent.stepTape clauses rows repeats hupper hij designated o
      ⟨StoppedProjectedBucketIndex.key (n := n) rows hrows base, tape⟩) event
  have hevent :
      StoppedProjectedUsefulAverage.bucketEvent clauses rows repeats hupper hij designated
        hbranch hrows flag σ κ o base direction =
      fun tape => event (StoppedProjectedUsefulEvent.stepTape clauses rows repeats hupper hij designated o
        ⟨StoppedProjectedBucketIndex.key (n := n) rows hrows base, tape⟩) := by
    funext tape
    rfl
  exact (congrArg
    (StoppedProjectedBucketIndex.tapeLaw clauses rows repeats hupper hij designated hrows o base).probability
    hevent).trans hp.symm

theorem original_probability_eq_usefulProbability_oai :
    (S o).original.probability (fun x => HierarchicalUsefulFamily.usefulEvent S κ
      (StoppedProjectedUsefulEvent.upperEvent clauses rows repeats hupper hij designated
        hbranch hrows flag σ) ⟨o, x⟩) =
      StoppedProjectedBuckets.usefulProbability clauses rows repeats hupper hij designated
        hrows o hbranch flag σ κ :=
  (StoppedProjectedUsefulAverage.original_probability_eq_mean clauses rows repeats hupper hij
    designated hbranch hrows flag σ κ o).trans
      (mean_eq_usefulProbability clauses rows repeats hupper hij designated hbranch hrows flag σ κ o)

end
end PerfectCompleteness.StoppedProjectedUsefulProbability

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.StoppedProjectedUsefulProbability.original_probability_eq_usefulProbability_oai := @OAI.PerfectCompleteness.StoppedProjectedUsefulProbability.original_probability_eq_usefulProbability_oai
