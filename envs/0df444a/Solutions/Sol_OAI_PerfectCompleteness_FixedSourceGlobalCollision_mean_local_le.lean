-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedSourceGlobalCollision.mean_local_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:22:15.463649+00:00
-- url     : https://prove2.me/submissions/6fd99f66-9444-4669-8920-de1ba7f25e11

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
import Theorems.Thm_OAI_PerfectCompleteness_ChildFiniteCallCollisionTransfer_marked_restricted_le_uniform_full
import Theorems.Thm_OAI_PerfectCompleteness_FixedSourceGlobalCollision_globalProbability_le_marked
import Theorems.Thm_OAI_PerfectCompleteness_FixedSourceLowerCollision_supported_uniform_le
import Theorems.Thm_OAI_PerfectCompleteness_SourceChildMarkedLaw_original_extended_marked_law

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_TwoResponseCollisionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.DecoderTableAdmissibility

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem expectation_le_of_support (μ : FiniteDistribution Ω) (score : Ω → ℝ)
    (bound : ℝ) (hbound : ∀ x, μ.weight x ≠ 0 → score x ≤ bound) :
    μ.expectation score ≤ bound := by
  calc
    _ ≤ ∑ x, μ.weight x * bound := by
      apply Finset.sum_le_sum
      intro x _
      by_cases hx : μ.weight x = 0
      · simp only [hx, zero_mul, le_refl]
      · exact mul_le_mul_of_nonneg_left (hbound x hx) (μ.nonnegative x)
    _ = bound := by rw [← Finset.sum_mul, μ.normalized, one_mul]

end FiniteLaw

end
end PerfectCompleteness.DecoderTableAdmissibility



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

theorem bound_pos (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    0 < bound branch n t calls rows :=
  lt_of_lt_of_le (Nat.card_pos (α := Raw calls rows slots)) (card_le calls rows slots)

end
end PerfectCompleteness.ChildBlockCardinality


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_ChildCallNumbering
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildCallNumbering

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {C : Type*} [Fintype C] {branch : Nat → Nat} {n t : Nat}

omit [Fintype C] in
theorem pullback_cast (rows : Nat → Nat)
    {slots target projected : Slots branch n → Fin t → MixedSupport.Slot}
    (h : slots = target)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (x : Raw (C := C) rows projected) :
    cast (congrArg (Raw (C := C) rows) h) (pullback rows p x) =
      pullback rows
        (cast (congrArg
          (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
            ∀ s k, MixedSupport.Projection (ss s k) (projected s k)) h) p) x := by
  cases h
  rfl

end
end PerfectCompleteness.ChildCallNumbering

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
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

end PerfectCompleteness.ChildBlockCardinality


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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedCallBudgetLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
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


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedComparisonErrorsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.FixedStoppedDecoderContext.upper_height _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerNode_height _root_.OAI.PerfectCompleteness.FixedStoppedNativeProjection.flags_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FixedComparisonErrors

open FixedParameters ChildBlockCardinality

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem comparison_errors {retained : Nat} (hcalls : retained ≤ calls p.plan)
    (height : Nat) :
    let L : ℝ := bound (branch p) height (FixedRows.sourceLength p.plan hδ)
      retained (FixedRows.rows p.plan)
    let m := p.cubeSize height
    Real.sqrt (L ^ 2 / (m : ℝ) ^ 3) / 2 < p.accuracy ∧
      Real.sqrt ((1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1) / 2 < p.accuracy ∧
      2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) < p.accuracy := by
  let L : ℝ := bound (branch p) height (FixedRows.sourceLength p.plan hδ)
    retained (FixedRows.rows p.plan)
  let B : ℝ := bound (branch p) height (FixedRows.sourceLength p.plan hδ)
    (calls p.plan) (FixedRows.rows p.plan)
  let m := p.cubeSize height
  have hL : 0 ≤ L := Nat.cast_nonneg _
  have hB : 0 ≤ B := Nat.cast_nonneg _
  have hLB : L ≤ B := by
    dsimp only [L, B]
    exact_mod_cast FixedCallBudget.child_bound_mono hcalls (branch p) height
      (FixedRows.sourceLength p.plan hδ) (FixedRows.rows p.plan)
  have hsq : L ^ 2 ≤ B ^ 2 := (sq_le_sq₀ hL hB).mpr hLB
  have hm : (2 : ℝ) ≤ m := by exact_mod_cast (p.cube_errors height).1
  have hm2 : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
  have hprob : (1 : ℝ) / (m : ℝ) ^ 2 < 1 := by
    apply (div_lt_one hm2).mpr
    nlinarith
  have hfixed := (p.cube_errors height).2
  change Real.sqrt (L ^ 2 / (m : ℝ) ^ 3) / 2 < p.accuracy ∧
    Real.sqrt ((1 + L ^ 2 / (m : ℝ) ^ 4) ^ (m ^ 3) - 1) / 2 < p.accuracy ∧
    2 * ((1 / (m : ℝ) ^ 2) * L / (1 - 1 / (m : ℝ) ^ 2)) < p.accuracy
  refine ⟨?_, ?_, ?_⟩
  · apply lt_of_le_of_lt _ hfixed.1
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right hsq (by positivity)
  · apply lt_of_le_of_lt _ hfixed.2.1
    apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
    apply Real.sqrt_le_sqrt
    apply sub_le_sub_right
    apply pow_le_pow_left₀ (by positivity)
    exact add_le_add_right
      (div_le_div_of_nonneg_right hsq
        (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 4)) 1
  · apply lt_of_le_of_lt _ hfixed.2.2.1
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hLB (by positivity)

end
end PerfectCompleteness.FixedComparisonErrors


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedProjectionErrorLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.FixedStoppedDecoderContext.upper_height _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerNode_height _root_.OAI.PerfectCompleteness.FixedStoppedNativeProjection.flags_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedProjectionError

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem sparse_error_lt {retained : Nat} (hcalls : retained ≤ calls p.plan)
    (height : Nat) :
    Real.sqrt ((1 + (projectionProbability p height : ℝ) ^ 2 *
      ((ChildBlockCardinality.bound (branch p) height (sourceLength p.plan hδ)
        retained (rows p.plan) : ℝ) - 1)) ^ branch p height - 1) / 2 < p.accuracy := by
  let L : ℝ := ChildBlockCardinality.bound (branch p) height (sourceLength p.plan hδ)
    retained (rows p.plan)
  let m : ℝ := p.cubeSize height
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (ChildBlockCardinality.shape_bound_pos (branch p) height
        (sourceLength p.plan hδ) retained (rows p.plan)))
  have hm4 : 0 ≤ m ^ 4 := by positivity
  have hbeta : (projectionProbability p height : ℝ) ^ 2 = 1 / m ^ 4 := by
    simp only [projectionProbability, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
      Rat.cast_natCast]
    dsimp only [m]
    ring
  have hbase : 1 + (projectionProbability p height : ℝ) ^ 2 * (L - 1) ≤
      1 + L ^ 2 / m ^ 4 := by
    rw [hbeta]
    have hsq : L - 1 ≤ L ^ 2 := by nlinarith
    have hdiv := div_le_div_of_nonneg_right hsq hm4
    calc
      1 + (1 / m ^ 4) * (L - 1) = 1 + (L - 1) / m ^ 4 := by ring
      _ ≤ 1 + L ^ 2 / m ^ 4 := by linarith
  have hnonneg : 0 ≤ 1 + (projectionProbability p height : ℝ) ^ 2 * (L - 1) := by
    have : 0 ≤ L - 1 := by linarith
    positivity
  have h := (FixedComparisonErrors.comparison_errors p hcalls height).2.1
  change Real.sqrt ((1 + (projectionProbability p height : ℝ) ^ 2 * (L - 1)) ^
    (p.cubeSize height ^ 3) - 1) / 2 < p.accuracy
  apply lt_of_le_of_lt _ h
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  apply Real.sqrt_le_sqrt
  exact sub_le_sub_right (pow_le_pow_left₀ hnonneg hbase _) 1

end
end PerfectCompleteness.FixedProjectionError

end

section

namespace PerfectCompleteness.FixedChildCollisionTransfer

noncomputable section

open scoped Classical
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)

theorem posterior_error_lt {retained : Nat}
    (hcalls : retained ≤ calls parameters.plan) (height : Nat) :
    2 * ((projectionProbability parameters height : ℝ) *
      (ChildBlockCardinality.bound (branch parameters) height
        (sourceLength parameters.plan hδ) retained (rows parameters.plan) : ℝ) /
      (1 - (projectionProbability parameters height : ℝ))) < parameters.accuracy := by
  have h := (FixedComparisonErrors.comparison_errors parameters hcalls height).2.2
  simpa only [projectionProbability, Rat.cast_div, Rat.cast_one, Rat.cast_pow,
    Rat.cast_natCast] using h

theorem lower_pair_calls_le {n height : Nat}
    (path : Path (branch parameters) n (height + 1)) (hn : n ≤ parameters.plan.depth) :
    Fintype.card (Option
      (WholeCutCalls.Index (rows parameters.plan) (repeats parameters.plan) path)) ≤
      calls parameters.plan := by
  have h := FixedCallBudget.modified_calls_le (rows parameters.plan)
    (repeats parameters.plan) path hn
  rw [Fintype.card_option]
  unfold calls
  omega

variable {height : Nat} {C : Type*} [Fintype C]
  {Z : Fin (branch parameters height) → Type*} [∀ i, Fintype (Z i)]

theorem marked_restricted_lt_uniform_full
    (hcalls : Fintype.card C ≤ calls parameters.plan)
    (slots : Slots (branch parameters) (height + 1) →
      Fin (sourceLength parameters.plan hδ) → MixedSupport.Slot)
    (projected : (i : Fin (branch parameters height)) → Z i →
      Slots (branch parameters) height → Fin (sourceLength parameters.plan hδ) →
        MixedSupport.Slot)
    (projection : ∀ i z s k, MixedSupport.Projection
      (childSlots slots i s k) (projected i z s k))
    (choiceLaw : (i : Fin (branch parameters height)) → FiniteDistribution (Z i))
    (F₀ F₁ : CutChildGrouping.Raw (C := C) slots (rows parameters.plan) →
      Option (ChildBilinearCollisionTransfer.ParentForm slots)) :
    (SparseReplacement.markedLaw
        (fun i => FiniteDistribution.uniform
          (ChildCallNumbering.Raw (C := C) (rows parameters.plan) (childSlots slots i)))
        (ChildCallNumberingLaws.replacementLaws (C := C) (rows parameters.plan)
          (childSlots slots) projected projection choiceLaw)
        (projectionProbability parameters height : ℝ)
        (by exact_mod_cast (projectionProbability_bounds parameters height).1.le)
        (by exact_mod_cast (projectionProbability_bounds parameters height).2.le)).probability
      (fun z => BilinearCollisionTransfer.restrictedCollision
        (F₀ z.2) (F₁ z.2) (ChildUnmarkedSpace.space slots z.1)) <
      (CutChildGrouping.rawLaw (C := C) slots (rows parameters.plan)).probability
        (fun raw => BilinearCollisionTransfer.fullCollision (F₀ raw) (F₁ raw)) +
          2 * parameters.accuracy := by
  have hβ : 0 ≤ (projectionProbability parameters height : ℝ) := by
    exact_mod_cast (projectionProbability_bounds parameters height).1.le
  have hβ' : (projectionProbability parameters height : ℝ) < 1 := by
    exact_mod_cast (projectionProbability_bounds parameters height).2
  have htransfer := ChildFiniteCallCollisionTransfer.marked_restricted_le_uniform_full
    (C := C) (rows parameters.plan) slots projected projection choiceLaw
    (projectionProbability parameters height : ℝ) hβ hβ' F₀ F₁
  have hposterior := posterior_error_lt parameters hcalls height
  have hvariation := FixedProjectionError.sparse_error_lt parameters hcalls height
  change _ < (FiniteProduct.law (fun i => FiniteDistribution.uniform
    (ChildCallNumbering.Raw (C := C) (rows parameters.plan) (childSlots slots i)))).probability
      (fun raw => BilinearCollisionTransfer.fullCollision (F₀ raw) (F₁ raw)) +
        2 * parameters.accuracy
  linarith

end
end PerfectCompleteness.FixedChildCollisionTransfer

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_SourceChildMarkedLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildMarkedLaw

open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays SourceChildKernel
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

omit [Fintype C] in
theorem nativeEquiv_pullback
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t))
    (block : Projected (C := C) (t := t) rows clauses designated i (childSource designated q i z)) :
    nativeEquiv rows clauses designated q i z
        (SourceChildNativeLaw.pullback rows clauses designated i (childSource designated q i z) true block) =
      ChildCallNumbering.pullback rows (questionProjection clauses designated q i z) block :=
  ChildCallNumbering.pullback_cast rows (nativeSlots_childSource clauses designated q i z)
    (projection clauses designated i (childSource designated q i z) true) block

theorem replacementAt_eq_liftedLaw
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (i : Fin (branch n)) (z : Choice (branch := branch) (n := n) (t := t)) :
    replacementAt (C := C) rows clauses designated q i z =
      ChildCallNumberingLaws.liftedLaw (C := C) rows (questionProjection clauses designated q i z) := by
  let μ : FiniteDistribution
      (Projected (C := C) (t := t) rows clauses designated i (childSource designated q i z)) :=
    FiniteDistribution.uniform _
  let f : Projected (C := C) (t := t) rows clauses designated i (childSource designated q i z) →
      Native (C := C) (t := t) rows clauses designated i (childSource designated q i z) :=
    fun block => SourceChildNativeLaw.pullback rows clauses designated i
      (childSource designated q i z) true block
  let g : Native (C := C) (t := t) rows clauses designated i (childSource designated q i z) →
      CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i :=
    nativeEquiv rows clauses designated q i z
  exact (FiniteDistribution.pushforward_comp μ f g).trans
    (congrArg (fun k : Projected (C := C) (t := t) rows clauses designated i
        (childSource designated q i z) →
        CutChildGrouping.Child (C := C) (questionSlots clauses q) rows i => μ.pushforward k)
      (funext fun block => nativeEquiv_pullback rows clauses designated q i z block))

theorem replacementLaws_eq
    (q : Questions (branch := branch) (n := n) (t := t) (m := m)) :
    replacementLaws (C := C) rows clauses designated q =
      ChildCallNumberingLaws.replacementLaws (C := C) rows (childSlots (questionSlots clauses q))
        (projectedSlots clauses designated q) (questionProjection clauses designated q)
        (fun _ => FiniteDistribution.uniform (Choice (branch := branch) (n := n) (t := t))) := by
  funext i
  unfold replacementLaws ChildCallNumberingLaws.replacementLaws ChildCallNumberingLaws.mixtureLaw
  apply congrArg (FiniteDistribution.mixture
    (FiniteDistribution.uniform (Choice (branch := branch) (n := n) (t := t))))
  funext z
  exact replacementAt_eq_liftedLaw rows clauses designated q i z

end
end PerfectCompleteness.SourceChildMarkedLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedSourceChildCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourceChildCollision

noncomputable section

open scoped Classical BigOperators
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {n height v m : Nat} [NeZero m]
  (path : Path (branch parameters) n (height + 1))
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch parameters height) → Slots (branch parameters) height)

variable (F₀ F₁ : (q : Questions (m := m) parameters (height := height)) →
  Native parameters path clauses q → Option (Form parameters clauses q))

private theorem expectation_add_const {A : Type*} [Fintype A]
    (μ : FiniteDistribution A) (f : A → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x + c) = μ.expectation f + c := by
  simp only [FiniteDistribution.expectation, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, μ.normalized, one_mul]

theorem restricted_probability_le (hn : n ≤ parameters.plan.depth) :
    (markedLaw parameters path clauses designated).probability
        (restrictedEvent parameters path clauses designated F₀ F₁) ≤
      (uniformLaw parameters path clauses).probability
        (fullEvent parameters path clauses F₀ F₁) + 2 * parameters.accuracy := by
  have hβ : 0 ≤ (projectionProbability parameters height : ℝ) := by
    exact_mod_cast (projectionProbability_bounds parameters height).1.le
  have hβ' : (projectionProbability parameters height : ℝ) ≤ 1 := by
    exact_mod_cast (projectionProbability_bounds parameters height).2.le
  have hlaw := SourceChildMarkedLaw.original_extended_marked_law
    (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses designated
    (repeats parameters.plan) path (projectionProbability parameters height : ℝ) hβ hβ'
  have hprob := congrArg
    (fun μ : FiniteDistribution
      (SourceChildMarkedLaw.Observation (C := Calls parameters path)
        (t := sourceLength parameters.plan hδ) (rows parameters.plan) clauses) =>
      μ.probability (fun record => BilinearCollisionTransfer.restrictedCollision
        (F₀ record.1 record.2.2) (F₁ record.1 record.2.2)
        (ChildUnmarkedSpace.space (SourceChildMarkedLaw.questionSlots clauses record.1)
          record.2.1))) hlaw
  rw [FiniteDistribution.probability_pushforward,
    CompletionSoundness.sigmaLaw_probability] at hprob
  rw [show (markedLaw parameters path clauses designated).probability
      (restrictedEvent parameters path clauses designated F₀ F₁) = _ from hprob]
  rw [uniformLaw, CompletionSoundness.sigmaLaw_probability]
  have hpoint := fun q : Questions (m := m) parameters (height := height) =>
    (FixedChildCollisionTransfer.marked_restricted_lt_uniform_full parameters
      (FixedChildCollisionTransfer.lower_pair_calls_le parameters path hn)
      (SourceChildMarkedLaw.questionSlots clauses q)
      (SourceChildMarkedLaw.projectedSlots clauses designated q)
      (SourceChildMarkedLaw.questionProjection clauses designated q)
      (fun _ => FiniteDistribution.uniform
        (SourceChildMarkedLaw.Choice (branch := branch parameters) (n := height)
          (t := sourceLength parameters.plan hδ)))
      (F₀ q) (F₁ q)).le
  have havg := SmallBias.expectation_mono
    (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
      (t := sourceLength parameters.plan hδ) (m := m)) hpoint
  rw [expectation_add_const] at havg
  simpa only [← SourceChildMarkedLaw.replacementLaws_eq, fullEvent] using havg

end
end PerfectCompleteness.FixedSourceChildCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedSourceLowerCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedSourceLowerCollision

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

variable
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots path outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1) bg → Prop)
  (density : ℝ)

private theorem expectation_add_const {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (f : X → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x + c) = μ.expectation f + c := by
  simp only [FiniteDistribution.expectation, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, μ.normalized, one_mul]

local instance rowSpaceFintype_rb08f79_1 (q : Questions (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.FixedSourceLowerCollision.upperAnswerFintype
attribute [local instance] OAI.PerfectCompleteness.FixedSourceLowerCollision.tableFintype
attribute [local instance] OAI.PerfectCompleteness.FixedSourceLowerCollision.directionNonempty
theorem mean_marked_le (hdensity : 0 < density) :
    (tableLaw parameters path outside clauses upper σ useful density).expectation
      (fun tables => (FiniteDistribution.uniform
        (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
          (markedProbability parameters path outside placeholder clauses designated upper d hnode
            A exterior tables)) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  apply DecoderTableAdmissibility.expectation_le_of_support
  intro tables hsupport
  have hpoint : ∀ direction : BucketSampler.Direction (rows parameters.plan (height + 1)),
      markedProbability parameters path outside placeholder clauses designated upper d hnode
          A exterior tables direction ≤
        uniformProbability parameters path outside placeholder clauses upper d hnode
          A exterior tables direction + 2 * parameters.accuracy := by
    intro direction
    exact FixedSourceChildCollision.restricted_probability_le parameters path clauses designated
      (first parameters path outside placeholder clauses upper d hnode A exterior tables)
      (second parameters path outside placeholder clauses upper d hnode A exterior tables direction)
      le_rfl
  have hmean := SmallBias.expectation_mono
    (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))) hpoint
  rw [expectation_add_const] at hmean
  have huniform := supported_uniform_le parameters path outside placeholder clauses upper d hnode A exterior
    σ useful density hdensity tables hsupport
  linarith

end
end PerfectCompleteness.FixedSourceLowerCollision

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

local instance rowSpaceFintype_rb08f79_2 (q : Questions (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.FixedSourceGlobalCollision.upperAnswerFintype
attribute [local instance] OAI.PerfectCompleteness.FixedSourceGlobalCollision.tableFintype
attribute [local instance] OAI.PerfectCompleteness.FixedSourceGlobalCollision.directionNonempty
theorem globalProbability_eq_local
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (direction : BucketSampler.Direction (rows parameters.plan (height + 1))) :
    globalProbability parameters path outside placeholder clauses designated upper d A
        exterior tables direction =
      (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
        (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
          localProbability parameters path outside placeholder clauses designated upper d A
            exterior q (tables q) direction) := by
  simp only [globalProbability, localProbability, SourceQuestionCollisionTransport.globalRestricted,
    SourceQuestionCollisionTransport.firstAnswer, SourceQuestionCollisionTransport.secondAnswer,
    localTables, Function.update_self]

variable
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth
    (sourceLength parameters.plan hδ)))
  (useful : (q : Questions (m := m) parameters (height := height)) →
    (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan)
      (SourceQuestionLowerForms.slots path outside clauses q) upper) →
    HierarchicalFrozenTables.QuotientMatrix
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1) bg → Prop)
  (density : ℝ)

include hnode in
theorem mean_global_le (hdensity : 0 < density) :
    (FixedSourceLowerCollision.tableLaw parameters path outside clauses upper σ useful density).expectation
      (fun tables => (FiniteDistribution.uniform
        (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
          (globalProbability parameters path outside placeholder clauses designated upper d A
            exterior tables)) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  apply le_trans _ (FixedSourceLowerCollision.mean_marked_le parameters path outside placeholder clauses
    designated upper d hnode A exterior σ useful density hdensity)
  apply SmallBias.expectation_mono
  intro tables
  apply SmallBias.expectation_mono
  intro direction
  exact globalProbability_le_marked parameters path outside placeholder clauses designated upper d hnode A
    exterior tables direction

include hnode in

theorem mean_local_le_oai (hdensity : 0 < density) :
    (FiniteDistribution.uniform
      (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation (fun direction =>
        (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
          (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
            (HierarchicalAllDecoderTables.upperTableLaw
              (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1)
              σ (useful q) adviceRows density).expectation (fun table =>
                localProbability parameters path outside placeholder clauses designated upper d A
                  exterior q table direction))) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 +
        2 * parameters.accuracy := by
  have h := mean_global_le parameters path outside placeholder clauses designated upper d hnode A exterior
    σ useful density hdensity
  have hglobal : ∀ tables : TableFamily parameters path outside clauses upper
        (adviceRows := adviceRows),
      globalProbability parameters path outside placeholder clauses designated upper d A
          exterior tables =
        fun direction => (PreliminarySampler.questionsLaw
          (branch := branch parameters) (n := height + 1)
          (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
            localProbability parameters path outside placeholder clauses designated upper d A
              exterior q (tables q) direction) := by
    intro tables
    funext direction
    exact globalProbability_eq_local parameters path outside placeholder clauses designated upper d A
      exterior tables direction
  simp_rw [hglobal] at h
  rw [FiniteDistribution.expectation_comm] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply FiniteDistribution.expectation_congr
  intro direction
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro q
  exact (FiniteProduct.expectation_eval
    (fun q => HierarchicalAllDecoderTables.upperTableLaw
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1)
      σ (useful q) adviceRows density) q
    (fun table => localProbability parameters path outside placeholder clauses designated upper d A
      exterior q table direction)).symm

end
end PerfectCompleteness.FixedSourceGlobalCollision

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedSourceGlobalCollision.mean_local_le_oai := @OAI.PerfectCompleteness.FixedSourceGlobalCollision.mean_local_le_oai
