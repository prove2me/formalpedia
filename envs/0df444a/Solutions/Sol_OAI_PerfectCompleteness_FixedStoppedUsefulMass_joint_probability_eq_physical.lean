-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:59.035684+00:00
-- url     : https://prove2.me/submissions/db84f382-254b-4f9d-9457-d53ce52a8806

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
import Theorems.Thm_OAI_PerfectCompleteness_StoppedProjectedExperiment_physicalFiber_probability
import Theorems.Thm_OAI_PerfectCompleteness_WholeCutGroupedProjection_evaluateGrouped_pullback

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

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_HierarchicalMatrixTable
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalMatrixTable

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (node : Nodes branch n)

theorem nativeRows_matrix (arrays : Arrays slots rows) :
    nativeRows slots node (NodeEmbedding.matrix arrays node) = arrays node := by
  funext i
  change (NodeEmbedding.equiv slots node).symm
    (EvaluationMatrix.rows (NodeEmbedding.RowSpace slots node)
      (EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots node)
        (NodeEmbedding.embeddedRows arrays node)) i) = arrays node i
  rw [EvaluationMatrix.rows_ofRows]
  exact (NodeEmbedding.equiv slots node).symm_apply_apply _

theorem assemble_original (arrays : Arrays slots rows) :
    assemble slots node (backgroundOf slots node arrays) (NodeEmbedding.matrix arrays node) = arrays := by
  funext j
  by_cases hj : j = node
  · subst j
    rw [assemble_selected, nativeRows_matrix]
  · simp only [assemble, dite_eq_right hj, backgroundOf]

theorem displayed_original (arrays : Arrays slots rows) :
    displayed slots node (backgroundOf slots node arrays) (NodeEmbedding.matrix arrays node) =
      TreeCanonical.numberedFunction slots (fullJoint arrays) := by
  unfold displayed
  rw [assemble_original]

end
end PerfectCompleteness.HierarchicalMatrixTable

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PrefixTests
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PrefixTests

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n cutoff : Nat}

variable {v m t : Nat} {rows : Nat → Nat}

theorem observe_choiceAt_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (q : PreliminarySampler.Questions branch n t m)
    (arrays : Arrays (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)) rows)
    (leaf : Slots branch n) (level : Fin n) (direction : LevelDirection rows level) :
    PreliminaryStrategy.observe clauses σ (q, leaf) arrays (choiceAt rows leaf level direction) =
      observeAtLevelNode clauses σ q arrays level (levelNode leaf level) direction := rfl

end
end PerfectCompleteness.PrefixTests

end

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

theorem nodeAtLevel_endpoint : {n k : Nat} → (p : Path branch n (k + 1)) →
    (suffix : Slots branch (k + 1)) →
    GeometricPath.nodeAtLevel (p.slotEmbedding suffix)
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ =
      WholeArrayInteriorExterior.upperNode p
  | _, _, .refl _, suffix => GeometricPath.nodeAtLevel_last suffix
  | N + 1, k, .step i p, suffix => by
      change GeometricPath.nodeAtLevel (branch := branch) (n := N + 1) (i, p.slotEmbedding suffix)
          (⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ : Fin N).castSucc =
        Sum.inr (i, WholeArrayInteriorExterior.upperNode p)
      exact (GeometricPath.nodeAtLevel_castSucc (branch := branch) (n := N)
        (i, p.slotEmbedding suffix)
        (⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ : Fin N)).trans
          (congrArg (fun node : Nodes branch N =>
            (Sum.inr (i, node) : Nodes branch (N + 1))) (nodeAtLevel_endpoint p suffix))

theorem pathTapeEquiv_law {t : Nat} (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (h : p = q) :
    (WholeArraySampler.tapeLaw rows repeats p.2 slots).pushforward
        (pathTapeEquiv rows repeats slots h) =
      WholeArraySampler.tapeLaw rows repeats q.2 slots := by
  cases h
  exact FiniteDistribution.pushforward_id _

theorem evaluate_pathTapeEquiv {t : Nat} (rows repeats : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (h : p = q)
    (ω : WholeArraySampler.Tape rows repeats p.2 slots) :
    WholeArraySampler.evaluate rows repeats q.2 slots
        (pathTapeEquiv rows repeats slots h ω) =
      WholeArraySampler.evaluate rows repeats p.2 slots ω := by
  cases h
  rfl

end
end PerfectCompleteness.StoppedOwnInputGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_PrefixMatrixAcceptance
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PrefixMatrixAcceptance

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {v m n t : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (questions : PreliminarySampler.Questions branch n t m)

local notation "slots" => sourceSlots clauses (PreliminarySampler.endpoints questions)

theorem observe_iff_lower
    (arrays : Arrays slots rows) (level : Fin n)
    (node : PrefixTests.LevelNode branch level)
    (a : PrefixTests.LevelDirection rows level) (upper : Nodes branch n) :
    PrefixTests.observeAtLevelNode clauses σ questions arrays level node a = true ↔
      HierarchicalPrediction.LowerAccepts slots upper
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) σ node.val
        (PrefixTests.nodeDirection rows level node a).val
        (NodeEmbedding.matrix arrays upper) := by
  unfold HierarchicalPrediction.LowerAccepts
  rw [HierarchicalMatrixTable.displayed_original]
  unfold PrefixTests.observeAtLevelNode
  dsimp only
  constructor
  · intro hevent
    exact @of_decide_eq_true _ _ hevent
  · intro haccept
    exact @decide_eq_true _ _ haccept

theorem observe_eq_lower
    (arrays : Arrays slots rows) (level : Fin n)
    (node : PrefixTests.LevelNode branch level)
    (a : PrefixTests.LevelDirection rows level) (upper : Nodes branch n) :
    PrefixTests.observeAtLevelNode clauses σ questions arrays level node a =
      decide (HierarchicalPrediction.LowerAccepts slots upper
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) σ node.val
        (PrefixTests.nodeDirection rows level node a).val
        (NodeEmbedding.matrix arrays upper)) := by
  apply Bool.eq_iff_iff.mpr
  simpa only [decide_eq_true_eq] using
    observe_iff_lower clauses σ questions arrays level node a upper

theorem observe_endpoint {k : Nat} (p : Path branch n (k + 1))
    (suffix : Slots branch (k + 1)) (arrays : Arrays slots rows)
    (a : PrefixTests.LevelDirection rows
      (⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ : Fin n)) :
    PreliminaryStrategy.observe clauses σ (questions, p.slotEmbedding suffix) arrays
      (PrefixTests.choiceAt rows (p.slotEmbedding suffix)
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ a) =
      PrefixTests.observeAtLevelNode clauses σ questions arrays
        ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩
        ⟨WholeArrayInteriorExterior.upperNode p,
          WholeArrayInteriorExterior.upperNode_height p⟩ a := by
  rw [PrefixTests.observe_choiceAt_eq]
  apply congrArg (fun node => PrefixTests.observeAtLevelNode clauses σ questions arrays
    ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) p.height_le⟩ node a)
  apply Subtype.ext
  exact StoppedOwnInputGeometry.nodeAtLevel_endpoint p suffix

end
end PerfectCompleteness.PrefixMatrixAcceptance

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

end
end PerfectCompleteness.CutProjectionAssembly

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutProjectionGeometry

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem childPullback_heq {C : Type*} [Fintype C] (rows : Nat → Nat)
    {left right left' right' : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (hL : left = left') (hR : right = right')
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (q' : ∀ s k, MixedSupport.Projection (left' s k) (right' s k))
    (hq : ∀ s k, HEq (q s k) (q' s k)) (i : Fin (branch n))
    (block : CutChildGrouping.Child (C := C) right rows i)
    (block' : CutChildGrouping.Child (C := C) right' rows i)
    (hb : HEq block block') :
    HEq (ChildAssemblyProjection.childPullback rows q i block)
      (ChildAssemblyProjection.childPullback rows q' i block') := by
  cases hL
  cases hR
  have hqq' : q = q' := by
    funext s k
    exact eq_of_heq (hq s k)
  cases hqq'
  have hbb' : block = block' := eq_of_heq hb
  cases hbb'
  rfl

private theorem keep_heq {a b : MixedSupport.Slot} (h : a = b) :
    HEq (MixedSupport.Projection.keep a) (MixedSupport.Projection.keep b) := by
  cases h
  rfl

theorem fillProjection_outside {m : Nat} (p : Path branch n m)
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch m → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (s : Slots branch n) (hout : s ∉ Set.range p.slotEmbedding) (k : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q s k)
      (MixedSupport.Projection.keep (CutSlotAssembly.fill p outside left s k)) := by
  revert outside left right q s hout k
  induction p with
  | refl _ =>
      intro outside left right q s hout k
      exact False.elim (hout ⟨s, rfl⟩)
  | step i p ih =>
      intro outside left right q s hout k
      obtain ⟨j, s⟩ := s
      by_cases hji : j = i
      · subst j
        have htail : s ∉ Set.range p.slotEmbedding := by
          rintro ⟨a, ha⟩
          exact hout ⟨a, congrArg (fun b => (i, b)) ha⟩
        have hfill : CutSlotAssembly.fill (.step i p) outside left (i, s) =
            CutSlotAssembly.fill p (fun b => outside (i, b)) left s :=
          ite_eq_left (show i = i from rfl)
        simp only [CutProjectionAssembly.fillProjection]
        exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
          ((ih (fun b => outside (i, b)) left right q s htail k).trans
            (keep_heq (congrFun hfill k).symm))
      · have hfill : CutSlotAssembly.fill (.step i p) outside left (j, s) = outside (j, s) :=
          ite_eq_right hji
        simp only [CutProjectionAssembly.fillProjection, dite_eq_right hji]
        exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
          (keep_heq (congrFun hfill k).symm)

end
end PerfectCompleteness.CutProjectionGeometry

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_WholeCutGroupedProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutGroupedProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem exteriorAt_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (placeholder left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder left external =
      WholeCutExteriorTransport.equiv rows repeats p
        (CutSlotAssembly.fill p outside right) (CutSlotAssembly.fill p outside left)
        (fun s h => (CutSlotAssembly.fill_outside_eq p outside left right s h).symm)
        (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external) := by
  apply eq_of_heq
  have hleft : HEq
      (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder left external) external :=
    cast_heq _ _
  have hright : HEq
      (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external) external :=
    cast_heq _ _
  exact hleft.trans ((cast_heq _ _).trans hright).symm

theorem fillChildren_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) right rows) :
    (fun i => CleanPhysicalReplay.fillChild rows repeats p outside left i
      ((ChildAssemblyProjection.rawPullback rows q children) i)) =
      ChildAssemblyProjection.rawPullback rows
        (CutGroupedProjection.cutProjection p
          (CutProjectionAssembly.fillProjection p outside left right q))
        (fun i => CleanPhysicalReplay.fillChild rows repeats p outside right i (children i)) := by
  funext i
  apply eq_of_heq
  exact (CleanPhysicalReplay.fillChild_heq rows repeats p outside left i
      ((ChildAssemblyProjection.rawPullback rows q children) i)).trans
    (CutProjectionGeometry.childPullback_heq rows
      (CleanPhysicalReplay.cutSlots_fill p outside left)
      (CleanPhysicalReplay.cutSlots_fill p outside right)
      (CutGroupedProjection.cutProjection p
        (CutProjectionAssembly.fillProjection p outside left right q)) q
      (CutProjectionAssembly.fillProjection_at_cut p outside left right q) i
      (CleanPhysicalReplay.fillChild rows repeats p outside right i (children i))
      (children i) (CleanPhysicalReplay.fillChild_heq rows repeats p outside right i
        (children i))).symm

theorem physicalTape_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (placeholder left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) right rows) :
    WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside left)
        (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder left external
          (ChildAssemblyProjection.rawPullback rows q children)) =
      ChildBlockProjection.arraysPullback rows
        (CutProjectionAssembly.fillProjection p outside left right q)
        (WholeCutSampler.evaluate rows repeats p (CutSlotAssembly.fill p outside right)
          (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder right external children)) := by
  change evaluateGrouped rows repeats p (CutSlotAssembly.fill p outside left)
      (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder left external)
      (fun i => CleanPhysicalReplay.fillChild rows repeats p outside left i
        ((ChildAssemblyProjection.rawPullback rows q children) i)) =
    ChildBlockProjection.arraysPullback rows
      (CutProjectionAssembly.fillProjection p outside left right q)
      (evaluateGrouped rows repeats p (CutSlotAssembly.fill p outside right)
        (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external)
        (fun i => CleanPhysicalReplay.fillChild rows repeats p outside right i (children i)))
  rw [exteriorAt_pullback rows repeats p outside placeholder left right external,
    fillChildren_pullback]
  exact evaluateGrouped_pullback rows repeats p
    (CutSlotAssembly.fill p outside left) (CutSlotAssembly.fill p outside right)
    (CutProjectionAssembly.fillProjection p outside left right q)
    (CutSlotAssembly.fill_outside_eq p outside left right)
    (CutProjectionGeometry.fillProjection_outside p outside left right q)
    (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external)
    (fun i => CleanPhysicalReplay.fillChild rows repeats p outside right i (children i))

end
end PerfectCompleteness.WholeCutGroupedProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GeometricPrefixSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FixedStoppedNativeProjection.flags_eq _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalCutCalls.card_refl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.StoppedProjectedContext.directions_split _root_.OAI.PerfectCompleteness.StoppedProjectedContext.questions_split _root_.OAI.PerfectCompleteness.StoppedProjectedContext.tag_split _root_.OAI.PerfectCompleteness.TerminalCalls.card_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_step _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_recursive _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_refl _root_.OAI.PerfectCompleteness.TerminalCalls.not_isTerminal_ordinary _root_.OAI.PerfectCompleteness.TerminalCalls.terminalSubtypeEquiv_apply _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutCalls.card_refl _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.GeometricPrefixSplit

open RecursiveSpaces DescendantSpaces
open GeometricCutSplit (Prefix PrefixDepth prefixPathDepth prefixPath castPath prefixLaw)
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

private theorem castPath_step {x y low : Nat} (h : x = y)
    (c : Fin (branch x)) (p : Path branch x low) :
    castPath (congrArg Nat.succ h) (.step c p) =
      .step (Equiv.cast (congrArg (fun n => Fin (branch n)) h) c)
        (castPath h p) := by
  cases h
  rfl

theorem depthEquiv_path (low b a : Nat)
    (x : PrefixDepth branch low (b + a)) :
    castPath (Nat.add_assoc low b a).symm (prefixPathDepth low (b + a) x) =
      (prefixPathDepth (low + b) a (depthEquiv low b a x).1).append
        (prefixPathDepth low b (depthEquiv low b a x).2) := by
  revert x
  induction a with
  | zero => intro x; rfl
  | succ a ih =>
      intro x
      change castPath (congrArg Nat.succ (Nat.add_assoc low b a).symm)
        (.step x.1 (prefixPathDepth low (b + a) x.2)) = _
      rw [castPath_step (Nat.add_assoc low b a).symm x.1
        (prefixPathDepth low (b + a) x.2)]
      exact congrArg (Path.step _) (ih x.2)

private theorem castPath_trans {x y z low : Nat} (h : x = y) (g : y = z)
    (p : Path branch x low) :
    castPath g (castPath h p) = castPath (h.trans g) p := by
  cases h
  cases g
  rfl

private theorem prefixPathDepth_cast {low d e : Nat} (h : d = e)
    (x : PrefixDepth branch low d) :
    prefixPathDepth low e (Equiv.cast (congrArg (PrefixDepth branch low) h) x) =
      castPath (congrArg (fun n => low + n) h) (prefixPathDepth low d x) := by
  cases h
  rfl

private theorem castPath_append {x y mid low : Nat} (h : x = y)
    (p : Path branch x mid) (q : Path branch mid low) :
    castPath h (p.append q) = (castPath h p).append q := by
  cases h
  rfl

private theorem castPath_depth_append {x y low : Nat} (h : x = y) (a : Nat)
    (upper : PrefixDepth branch x a) (lower : Path branch x low) :
    castPath (congrArg (fun n => n + a) h)
        ((prefixPathDepth x a upper).append lower) =
      (prefixPathDepth y a
        (Equiv.cast (congrArg (fun n => PrefixDepth branch n a) h) upper)).append
          (castPath h lower) := by
  cases h
  rfl

variable {root mid low : Nat}

theorem prefixPath_split (hlow : low ≤ mid) (hmid : mid ≤ root)
    (pref : Prefix branch root low) :
    prefixPath (hlow.trans hmid) pref =
      (prefixPath hmid (splitEquiv hlow hmid pref).1).append
        (prefixPath hlow (splitEquiv hlow hmid pref).2) := by
  let a := root - mid
  let b := mid - low
  have hd : root - low = b + a := by dsimp [a, b]; omega
  have hm : low + b = mid := Nat.add_sub_of_le hlow
  let x : PrefixDepth branch low (b + a) :=
    Equiv.cast (congrArg (PrefixDepth branch low) hd) pref
  calc
    prefixPath (hlow.trans hmid) pref =
        castPath (Nat.add_sub_of_le hmid)
          (castPath (congrArg (fun n => n + a) hm)
            (castPath (Nat.add_assoc low b a).symm
              (prefixPathDepth low (b + a) x))) := by
      dsimp only [x]
      rw [prefixPathDepth_cast hd pref]
      simp only [castPath_trans]
      rfl
    _ = castPath (Nat.add_sub_of_le hmid)
        (castPath (congrArg (fun n => n + a) hm)
          ((prefixPathDepth (low + b) a (depthEquiv low b a x).1).append
            (prefixPathDepth low b (depthEquiv low b a x).2))) := by
      rw [depthEquiv_path]
    _ = castPath (Nat.add_sub_of_le hmid)
        ((prefixPathDepth mid a
          (Equiv.cast (congrArg (fun n => PrefixDepth branch n a) hm)
            (depthEquiv low b a x).1)).append
          (castPath hm (prefixPathDepth low b (depthEquiv low b a x).2))) := by
      rw [castPath_depth_append]
    _ = (prefixPath hmid (splitEquiv hlow hmid pref).1).append
        (prefixPath hlow (splitEquiv hlow hmid pref).2) := by
      rw [castPath_append]
      rfl

theorem prefixPath_join (hlow : low ≤ mid) (hmid : mid ≤ root)
    (upper : Prefix branch root mid) (lower : Prefix branch mid low) :
    prefixPath (hlow.trans hmid) (joinEquiv hlow hmid (upper, lower)) =
      (prefixPath hmid upper).append (prefixPath hlow lower) := by
  simpa only [split_join] using
    prefixPath_split hlow hmid (joinEquiv hlow hmid (upper, lower))

end PerfectCompleteness.GeometricPrefixSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_SourcePhysicalTapeLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalTapeLaw

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

omit [NeZero m] in
theorem observeFiber_native_arrays
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (sample : SourcePhysicalWholeLaw.Raw rows repeats p outside placeholder clauses designated) :
    ChildBlockProjection.arraysPullback rows
        (fullProjection p outside clauses designated
          (sources, (observeFiber rows repeats p outside placeholder clauses designated sources sample).1))
        (WholeArraySampler.evaluate rows repeats p
          (projectedSlots p outside clauses designated
            (sources, (observeFiber rows repeats p outside placeholder clauses designated sources sample).1))
          (observeFiber rows repeats p outside placeholder clauses designated sources sample).2) =
      SourcePhysicalWholeLaw.observeLeft rows repeats p outside placeholder clauses designated sources sample :=
  (WholeCutGroupedProjection.physicalTape_pullback rows repeats p outside placeholder
    (SourceChildKernel.parentLeftSlots clauses designated sources)
    (SourceChildKernel.parentRightSlots rows clauses designated sources sample.2)
    (SourceChildKernel.parentProjection rows clauses designated sources sample.2) sample.1
    (SourceChildKernel.rightChildren rows clauses designated sources sample.2)).symm

end
end PerfectCompleteness.SourcePhysicalTapeLaw

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

theorem arrays_tapeRead (o : Outer (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : TapeSample clauses rows repeats hupper hij designated o) :
    (experiment clauses rows repeats hupper hij designated hbranch hrows flag σ o).arrays
        (tapeRead clauses rows repeats hupper hij designated o sample) =
      ChildBlockProjection.arraysPullback rows
        (projection clauses rows hupper hij designated o sample.1)
        (WholeArraySampler.evaluate rows repeats (stoppedPath rows hupper hij o sample.1)
          (projectedSlots clauses rows hupper hij designated o sample.1) sample.2) :=
  congrArg (ChildBlockProjection.arraysPullback rows
    (projection clauses rows hupper hij designated o sample.1))
    (StoppedOwnInputGeometry.evaluate_pathTapeEquiv rows repeats
      (projectedSlots clauses rows hupper hij designated o sample.1)
      (fullPath_spec rows hupper hij o sample.1).symm sample.2)

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedArrays
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedArrays

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private theorem sourceProjection_heq
    {branch : Nat → Nat} {i t v m : Nat}
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch i) → Slots branch i)
    (q : PreliminarySampler.Questions branch (i + 1) t m)
    (positions : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i))
    (leaf : Slots branch (i + 1)) (a : Fin t) :
    HEq (SourceProjectedTag.projection clauses designated q positions flags leaf a)
      (SourceChildKernel.projection clauses designated leaf.1
        (SourceQuestionKernelJoint.sources designated q positions leaf.1)
        (flags leaf.1) leaf.2 a) := by
  unfold SourceProjectedTag.projection
  dsimp only [id]
  exact mpr_heq _ _

private theorem fillProjection_heq
    {branch : Nat → Nat} {n h t : Nat} (p : Path branch n h)
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    {left left' right right' : Slots branch h → Fin t → MixedSupport.Slot}
    (hl : left = left') (hr : right = right')
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (q' : ∀ s a, MixedSupport.Projection (left' s a) (right' s a))
    (hq : ∀ s a, HEq (q s a) (q' s a)) (leaf : Slots branch n) (a : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q leaf a)
      (CutProjectionAssembly.fillProjection p outside left' right' q' leaf a) := by
  cases hl
  cases hr
  have he : q = q' := funext (fun s => funext (fun a => eq_of_heq (hq s a)))
  cases he
  rfl

private theorem arraysPullback_heq
    {branch : Nat → Nat} {n t : Nat} (rows : Nat → Nat)
    {left left' right : Slots branch n → Fin t → MixedSupport.Slot}
    (hl : left = left')
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (q' : ∀ s a, MixedSupport.Projection (left' s a) (right s a))
    (hq : ∀ s a, HEq (q s a) (q' s a)) (arrays : Arrays right rows) :
    HEq (ChildBlockProjection.arraysPullback rows q arrays)
      (ChildBlockProjection.arraysPullback rows q' arrays) := by
  cases hl
  have he : q = q' := funext (fun s => funext (fun a => eq_of_heq (hq s a)))
  cases he
  rfl

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

theorem projection_heq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : StoppedProjectedExperiment.PhysicalBase
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows)
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i))
    (leaf : Slots branch n) (a : Fin t) :
    HEq (StoppedProjectedExperiment.projection clauses rows hupper hij designated o
        (StoppedProjectedExperiment.withFlags rows base flags) leaf a)
      (SourcePhysicalTapeLaw.fullProjection
        (StoppedProjectedExperiment.stoppedPath rows hupper hij o
          (StoppedProjectedExperiment.baseTag rows base))
        (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
        (StoppedProjectedExperiment.physicalSources rows hupper hij designated o base, flags)
        leaf a) := by
  unfold StoppedProjectedExperiment.projection
  apply (CutProjectionAssembly.castProjection_heq _ _ _).trans
  exact fillProjection_heq
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows base))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.parentLeftSlots_sources clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows base)) base.2.1).symm
    rfl _ _
    (sourceProjection_heq clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows base)) base.2.1 flags) leaf a

variable [NeZero m]
  (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

omit [NeZero m] in
theorem arrays_physicalExperimentRead_heq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :
    HEq ((StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ o).arrays
      (StoppedProjectedExperiment.physicalExperimentRead clauses rows repeats hupper hij designated
        o sample))
      (physicalArrays clauses rows repeats hupper hij designated o sample) := by
  let observed := SourcePhysicalTapeLaw.observeFiber rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows sample.1))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1)))
    clauses designated
    (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1) sample.2
  have htable := StoppedProjectedExperiment.arrays_tapeRead clauses rows repeats hupper hij
    designated hbranch hrows flag σ o
    (StoppedProjectedExperiment.physicalRead clauses rows repeats hupper hij designated o sample)
  have hpull := arraysPullback_heq rows
    (nativeSlots_eq clauses rows hupper hij designated o sample.1).symm
    (StoppedProjectedExperiment.projection clauses rows hupper hij designated o
      (StoppedProjectedExperiment.withFlags rows sample.1 observed.1))
    (SourcePhysicalTapeLaw.fullProjection
      (StoppedProjectedExperiment.stoppedPath rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1))
      (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
      (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1, observed.1))
    (projection_heq clauses rows hupper hij designated o sample.1 observed.1)
    (WholeArraySampler.evaluate rows repeats
      (StoppedProjectedExperiment.stoppedPath rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1))
      (StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
        (StoppedProjectedExperiment.withFlags rows sample.1 observed.1)) observed.2)
  have hphysical := SourcePhysicalTapeLaw.observeFiber_native_arrays rows repeats
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows sample.1))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.originalSlots clauses
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows sample.1)))
    clauses designated
    (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1) sample.2
  exact (heq_of_eq htable).trans (hpull.trans (heq_of_eq hphysical))

omit [NeZero m] in
theorem arrays_physicalExperimentRead_eq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :
    (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ o).arrays
      (StoppedProjectedExperiment.physicalExperimentRead clauses rows repeats hupper hij designated
        o sample) =
      cast (congrArg
        (fun slots : Slots branch n → Fin t → MixedSupport.Slot => Arrays slots rows)
        (nativeSlots_eq clauses rows hupper hij designated o sample.1))
        (physicalArrays clauses rows repeats hupper hij designated o sample) := by
  apply eq_of_heq
  exact (arrays_physicalExperimentRead_heq clauses rows repeats hupper hij designated
    hbranch hrows flag σ o sample).trans (cast_heq _ _).symm

end
end PerfectCompleteness.StoppedProjectedArrays

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedProjectedGlobalLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedPhysicalLaw

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

variable [NeZero m]
  (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

theorem read_law :
    (law clauses rows repeats hupper hij designated hbranch hrows flag).pushforward
        (read clauses rows repeats hupper hij designated) =
      StoppedProjectedGlobalLaw.experimentLaw clauses rows repeats hupper hij designated
        hbranch hrows flag σ := by
  unfold law read
  rw [SigmaObservation.pushforward_fiber]
  unfold StoppedProjectedGlobalLaw.experimentLaw
  congr 1
  funext o
  exact StoppedProjectedExperiment.physicalExperimentRead_law
    clauses rows repeats hupper hij designated
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hupper)) hrows flag σ o

theorem probability_read
    (event : StoppedProjectedGlobalLaw.ExperimentSample (t := t)
      clauses rows repeats hupper hij designated → Bool) :
    (law clauses rows repeats hupper hij designated hbranch hrows flag).probability
        (fun sample => event (read clauses rows repeats hupper hij designated sample)) =
      (StoppedProjectedGlobalLaw.experimentLaw clauses rows repeats hupper hij designated
        hbranch hrows flag σ).probability event := by
  rw [← read_law clauses rows repeats hupper hij designated hbranch hrows flag σ,
    FiniteDistribution.probability_pushforward]

end
end PerfectCompleteness.StoppedProjectedPhysicalLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedUsefulMass
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedUsefulMass

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

variable (designated : Fin (FixedParameters.branch parameters i.val) →
  Slots (FixedParameters.branch parameters) i.val)

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

theorem lowerEvent_eq_win (o : Outer parameters j input)
    (x : OriginalFiber parameters i j hij input designated o) :
    HierarchicalAdviceExperiment.lowerEvent
        (experiment parameters i j hij input designated strategy o) x =
      StoppedSharedEvents.win (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k) i
        (originalRecord parameters i j hij input designated strategy ⟨o, x⟩) := by
  symm
  unfold StoppedSharedEvents.win StoppedSharedEvents.representativeLeaf originalRecord record
  dsimp only
  rw [GeometricPrefixSplit.prefixPath_join]
  exact (PrefixMatrixAcceptance.observe_endpoint (clauses input)
    (canonicalStrategy parameters input strategy) o.1
    (StoppedProjectedExperiment.stoppedPath (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij o x.1)
    (StoppedSharedEvents.referenceSuffix (Nat.succ_le_of_lt i.isLt)
      (fun k _ => FixedParameters.branch_pos parameters k))
    ((experiment parameters i j hij input designated strategy o).arrays x)
    (x.1.2.2 i)).trans
      (PrefixMatrixAcceptance.observe_eq_lower (clauses input)
        (canonicalStrategy parameters input strategy) o.1
        ((experiment parameters i j hij input designated strategy o).arrays x) i
        ⟨StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij o x.1,
          StoppedProjectedExperiment.lower_height (FixedRows.rows parameters.plan)
            (Nat.succ_le_of_lt j.isLt) hij o x.1⟩ (x.1.2.2 i)
        (StoppedProjectedExperiment.upper (Nat.succ_le_of_lt j.isLt) o))

theorem upperEvent_eq_win (o : Outer parameters j input)
    (x : OriginalFiber parameters i j hij input designated o) :
    upperEvent parameters i j hij input designated strategy o x =
      StoppedSharedEvents.win (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k) j
        (originalRecord parameters i j hij input designated strategy ⟨o, x⟩) := by
  symm
  unfold StoppedSharedEvents.win StoppedSharedEvents.representativeLeaf originalRecord record
  dsimp only
  rw [GeometricPrefixSplit.prefixPath_join, Path.slotEmbedding_append]
  exact PrefixMatrixAcceptance.observe_endpoint (clauses input)
    (canonicalStrategy parameters input strategy) o.1
    (StoppedProjectedExperiment.upperPath (Nat.succ_le_of_lt j.isLt) o)
    ((StoppedProjectedExperiment.lowerPath (FixedRows.rows parameters.plan) hij x.1).slotEmbedding
      (StoppedSharedEvents.referenceSuffix (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k)))
    ((experiment parameters i j hij input designated strategy o).arrays x) (x.1.2.2 j)

theorem originalRecord_physicalRead
    (sample : PhysicalSample parameters i j hij input designated) :
    originalRecord parameters i j hij input designated strategy
        (StoppedProjectedPhysicalLaw.read (clauses input) (FixedRows.rows parameters.plan)
          (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij designated sample) =
      physicalRecord parameters i j hij input designated sample := by
  exact congrArg (record parameters i j hij input sample.1 sample.2.1.1 sample.2.1.2.2)
    (StoppedProjectedArrays.arrays_physicalExperimentRead_eq (clauses input)
      (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij designated
      (fun k _ => FixedParameters.branch_pos parameters k)
      (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)
      (canonicalStrategy parameters input strategy) sample.1 sample.2)

theorem joint_probability_eq_physical_oai :
    (originalLaw parameters i j hij input designated strategy).probability
      (HierarchicalUsefulFamily.jointEvent
        (experiment parameters i j hij input designated strategy)
        (upperEvent parameters i j hij input designated strategy)) =
    (physicalLaw parameters i j hij input designated).probability (fun sample =>
      StoppedSharedEvents.pair (clauses input) strategy (Nat.succ_le_of_lt i.isLt)
        (fun k _ => FixedParameters.branch_pos parameters k) i j
        (physicalRecord parameters i j hij input designated sample)) := by
  have hevent : HierarchicalUsefulFamily.jointEvent
      (experiment parameters i j hij input designated strategy)
      (upperEvent parameters i j hij input designated strategy) =
      (fun sample => StoppedSharedEvents.pair (clauses input) strategy
        (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k) i j
        (originalRecord parameters i j hij input designated strategy sample)) := by
    funext sample
    exact congrArg₂ Bool.and
      (lowerEvent_eq_win parameters i j hij input designated strategy sample.1 sample.2)
      (upperEvent_eq_win parameters i j hij input designated strategy sample.1 sample.2)
  rw [hevent]
  have hread := StoppedProjectedPhysicalLaw.probability_read (clauses input)
    (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij designated
    (fun k _ => FixedParameters.branch_pos parameters k)
    (fun k => FixedPreliminaryGame.rows_pos parameters (k + 1)) (flags parameters i)
    (canonicalStrategy parameters input strategy)
    (fun sample => StoppedSharedEvents.pair (clauses input) strategy
      (Nat.succ_le_of_lt i.isLt) (fun k _ => FixedParameters.branch_pos parameters k) i j
      (originalRecord parameters i j hij input designated strategy sample))
  simpa only [originalRecord_physicalRead, originalLaw, physicalLaw] using hread.symm

end
end PerfectCompleteness.FixedStoppedUsefulMass

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical_oai := @OAI.PerfectCompleteness.FixedStoppedUsefulMass.joint_probability_eq_physical_oai
