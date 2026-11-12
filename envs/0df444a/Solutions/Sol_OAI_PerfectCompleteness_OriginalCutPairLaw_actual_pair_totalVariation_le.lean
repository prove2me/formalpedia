-- Prove2me | solution 1 for OAI.PerfectCompleteness.OriginalCutPairLaw.actual_pair_totalVariation_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:25:04.760194+00:00
-- url     : https://prove2.me/submissions/cbfbdd87-384f-4ca5-88e0-51004d38ede7

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
import Definitions.Def_OAIQ252P018
import Theorems.Thm_OAI_PerfectCompleteness_OriginalPrefixContinuation_raw_observed_variation

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_UniformLinearImage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UniformLinearImage

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem eq_uniform_of_weight_constant {A : Type*} [Fintype A] [Nonempty A]
    (μ : FiniteDistribution A) (constant : ∀ x y, μ.weight x = μ.weight y) :
    μ = FiniteDistribution.uniform A := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change μ.weight x = 1 / (Fintype.card A : ℝ)
  apply (eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  calc
    μ.weight x * (Fintype.card A : ℝ) = ∑ _y : A, μ.weight x := by
      simp [mul_comm]
    _ = ∑ y : A, μ.weight y := by
      apply Finset.sum_congr rfl
      intro y _
      exact constant x y
    _ = 1 := μ.normalized

theorem uniform_pushforward_weight {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] (f : A → B) (y : B) :
    ((FiniteDistribution.uniform A).pushforward f).weight y =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card A := by
  classical
  calc
    _ = ∑ x : A, if f x = y then (1 / (Fintype.card A : ℝ)) else 0 := by
      unfold FiniteDistribution.pushforward FiniteDistribution.uniform
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : f x = y <;> simp [h]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul, div_eq_mul_inv]

theorem uniform_pushforward_addHom {A B : Type*}
    [AddGroup A] [AddMonoid B] [Fintype A] [Fintype B]
    (f : A →+ B) (surjective : Function.Surjective f) :
    (FiniteDistribution.uniform A).pushforward f = FiniteDistribution.uniform B := by
  classical
  apply eq_uniform_of_weight_constant
  intro y z
  rw [uniform_pushforward_weight, uniform_pushforward_weight,
    AddMonoidHom.card_fiber_eq_of_mem_range f (surjective y) (surjective z)]

theorem uniform_pushforward_linearMap {R A B : Type*} [Semiring R]
    [AddCommGroup A] [AddCommMonoid B] [Module R A] [Module R B]
    [Fintype A] [Fintype B] (f : A →ₗ[R] B) (surjective : Function.Surjective f) :
    (FiniteDistribution.uniform A).pushforward f = FiniteDistribution.uniform B :=
  uniform_pushforward_addHom f.toAddMonoidHom surjective

end
end PerfectCompleteness.UniformLinearImage

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

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketUniformLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSamplerBiasAlgebra

open PointwiseSpaces RecursiveSpaces RecursiveSampler
open scoped BigOperators

universe u w

variable (𝕜 : Type w) [Field 𝕜]

variable {branch : Nat → Nat} {n : Nat}

noncomputable section

theorem combine_eq (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    combine 𝕜 A i r ordinary left right =
      (∑ j : OffPath i, childSquareLift 𝕜 A j.val (ordinary j)) +
        ∑ h : Fin r, childProduct 𝕜 A i (left h) (right h) := by
  apply Subtype.ext
  change combineFunction 𝕜 A i r ordinary left right =
    (space 𝕜 branch (n + 1) A).subtype
      ((∑ j : OffPath i, childSquareLift 𝕜 A j.val (ordinary j)) +
        ∑ h : Fin r, childProduct 𝕜 A i (left h) (right h))
  rw [map_add, map_sum, map_sum]
  rfl

end
end PerfectCompleteness.RecursiveSamplerBiasAlgebra



namespace PerfectCompleteness.RecursiveSampler

open PointwiseSpaces RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

variable (𝕜 : Type w) [Field 𝕜]

theorem stepCombine_splitEvaluatedTape (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (t : Tape 𝕜 repeats (.step i p) A) :
    stepCombine 𝕜 repeats i p A (splitEvaluatedTape 𝕜 repeats i p A t) =
      evaluate 𝕜 repeats (.step i p) A t := rfl

end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformChildSum
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.OddListExtraction.form_atom_self _root_.OAI.PerfectCompleteness.OddListExtraction.multiplicationForm_apply _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformChildSum

open scoped BigOperators
open PointwiseSpaces RecursiveSpaces UniformLinearImage
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {𝕜 X J : Type*} [Field 𝕜] [Fintype J]
  {D : J → Type*}

theorem childSum_surjective (r : ∀ i, X → D i)
    (H : ∀ i, Submodule 𝕜 (D i → 𝕜)) : Function.Surjective (childSum r H) := by
  classical
  intro u
  let p : J → Submodule 𝕜 (X → 𝕜) :=
    fun i => (squareSpace (H i)).map (pullback 𝕜 (r i))
  have hu : (u : X → 𝕜) ∈ ⨆ i ∈ (Finset.univ : Finset J), p i := by
    simpa [p, childSpace] using u.property
  obtain ⟨v, hv⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (s := Finset.univ) p (u : X → 𝕜)).mp hu
  have hx : ∀ i, ∃ w : squareSpace (H i),
      pullback 𝕜 (r i) (w : D i → 𝕜) = (v i : X → 𝕜) := by
    intro i
    obtain ⟨w, hw, heq⟩ := Submodule.mem_map.mp (v i).property
    exact ⟨⟨w, hw⟩, heq⟩
  choose w hw using hx
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change (∑ i, pullback 𝕜 (r i) (w i : D i → 𝕜)) = (u : X → 𝕜)
  calc
    _ = ∑ i, (v i : X → 𝕜) := Finset.sum_congr rfl (fun i _ => hw i)
    _ = _ := hv


variable {branch : Nat → Nat} {n : Nat}

theorem recursiveSum_surjective (A : Slots branch (n + 1) → Type*) :
    Function.Surjective (recursiveSum (𝕜 := 𝕜) A) :=
  childSum_surjective (childRestriction A) (fun i => space 𝕜 branch n (childFamily A i))

end
end PerfectCompleteness.UniformChildSum

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

theorem root_ne_lower (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (root : BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p))
    (lower : Index rows repeats p) :
    rootCall rows repeats i p root ≠ lowerCall rows repeats i p lower := by
  intro h
  cases h

theorem root_ne_ownBucket (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m)
    (root : BucketSampler.Direction (rows (n + 1)) × TerminalIndex repeats (.step i p))
    (own : BucketSampler.Direction (rows m)) :
    rootCall rows repeats i p root ≠ ownBucket rows repeats (.step i p) own :=
  root_ne_lower rows repeats i p root (ownBucket rows repeats p own)

end
end PerfectCompleteness.OriginalCutCalls

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutChildGrouping
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutChildGrouping

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

omit [Fintype C] in
theorem assemble_surjective : Function.Surjective (assemble (C := C) slots rows) := by
  rintro ⟨calls, arrays⟩
  have hex : ∀ q : C, ∃ u : (i : Fin (branch n)) → squareSpace (H (childSlots slots i)),
      UniformChildSum.recursiveSum (TreeSourceSpaces.LeafDomain slots) u = calls q := by
    intro q
    exact UniformChildSum.recursiveSum_surjective (TreeSourceSpaces.LeafDomain slots) (calls q)
  choose u hu using hex
  refine ⟨fun i => (fun q => u q i, arrays i), ?_⟩
  apply Prod.ext
  · funext q
    exact hu q
  · rfl

theorem assemble_law :
    (rawLaw (C := C) slots rows).pushforward (assemble slots rows) =
      FiniteDistribution.uniform (Assembled (C := C) slots rows) := by
  unfold rawLaw
  rw [UniformLinearImage.law_uniform]
  exact UniformLinearImage.uniform_pushforward_linearMap
    (assemble slots rows) (assemble_surjective slots rows)

end
end PerfectCompleteness.CutChildGrouping

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeCutSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutSampler

open TreeSourceSpaces HierarchicalArrays DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem uniform_product {R S : Type*} [Fintype R] [Fintype S]
    [Nonempty R] [Nonempty S] :
    (FiniteDistribution.uniform R).product (FiniteDistribution.uniform S) =
      FiniteDistribution.uniform (R × S) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.product, FiniteDistribution.uniform,
    Fintype.card_prod, Nat.cast_mul, one_div_mul_one_div]

end

end PerfectCompleteness.WholeCutSampler

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_DensityVariation
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

theorem variation_pushforward_le (μ ν : FiniteDistribution Ω) (observe : Ω → Γ) :
    (μ.pushforward observe).totalVariation (ν.pushforward observe) ≤
      μ.totalVariation ν := by
  classical
  unfold FiniteDistribution.totalVariation
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  have hdiff (y : Γ) :
      (μ.pushforward observe).weight y - (ν.pushforward observe).weight y =
        ∑ x, if observe x = y then μ.weight x - ν.weight x else 0 := by
    simp only [FiniteDistribution.pushforward, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : observe x = y <;> simp [hx]
  calc
    _ ≤ ∑ y, ∑ x, if observe x = y then |μ.weight x - ν.weight x| else 0 := by
      apply Finset.sum_le_sum
      intro y _
      rw [hdiff]
      calc
        _ ≤ ∑ x, |if observe x = y then μ.weight x - ν.weight x else 0| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          split <;> simp
    _ = _ := by rw [Finset.sum_comm]; simp

end
end PerfectCompleteness.DensityVariation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutBucketTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutBucketTransport

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}

attribute [local instance] OAI.PerfectCompleteness.CutBucketTransport.rowSpaceFintype
theorem nativeLaw_pushforward (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (hrows : 0 < rows (m + 1)) :
    (nativeLaw rows p slots hrows).pushforward (CutNodeRows.bucketSampleEquiv rows p slots) =
      HierarchicalAgreementMean.bucketLaw slots (upperNode p)
        (by simpa only [upperNode_height] using hrows) := by
  let : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  let : Nonempty (BucketSampler.Direction (rows (Nodes.height (upperNode p)))) :=
    ⟨CutNodeRows.directionEquiv rows p (BucketUniform.coordinateDirection ⟨0, hrows⟩)⟩
  unfold nativeLaw HierarchicalAgreementMean.bucketLaw
  simp only [BucketSampler.tapeLaw, UniformLinearImage.law_uniform,
    WholeCutSampler.uniform_product]
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (CutNodeRows.bucketSampleEquiv rows p slots)

end
end PerfectCompleteness.CutBucketTransport

end

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


namespace PerfectCompleteness.CommonProductVariation

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {S A Γ : Type*} [Fintype S] [Fintype A] [Fintype Γ]

theorem product_totalVariation (μ : FiniteDistribution S)
    (P Q : FiniteDistribution A) :
    (μ.product P).totalVariation (μ.product Q) = P.totalVariation Q := by
  change (∑ z : S × A,
    |μ.weight z.1 * P.weight z.2 - μ.weight z.1 * Q.weight z.2|) / 2 =
      (∑ a : A, |P.weight a - Q.weight a|) / 2
  rw [Fintype.sum_prod_type]
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (μ.nonnegative _), ← Finset.mul_sum]
  rw [← Finset.sum_mul, μ.normalized, one_mul]

theorem observed_product_le (μ : FiniteDistribution S)
    (P Q : FiniteDistribution A) (observe : S × A → Γ) :
    ((μ.product P).pushforward observe).totalVariation
      ((μ.product Q).pushforward observe) ≤ P.totalVariation Q :=
  (DensityVariation.variation_pushforward_le _ _ observe).trans_eq
    (product_totalVariation μ P Q)

theorem observed_product_le_of_bound (μ : FiniteDistribution S)
    (P Q : FiniteDistribution A) (observe : S × A → Γ)
    {error : ℝ} (herror : P.totalVariation Q ≤ error) :
    ((μ.product P).pushforward observe).totalVariation
      ((μ.product Q).pushforward observe) ≤ error :=
  (observed_product_le μ P Q observe).trans herror

end
end PerfectCompleteness.CommonProductVariation


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildScalarAssemblyLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OriginalChildScalarAssembly

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces
open OriginalChildScalars RecursiveSamplerBiasAlgebra
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem recursiveSum_eq_sum (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (values : (child : Fin (branch n)) → Square slots child) :
    UniformChildSum.recursiveSum (𝕜 := F2) (LeafDomain slots) values =
      ∑ child : Fin (branch n), childSquareLift F2 (LeafDomain slots) child (values child) := by
  apply Subtype.ext
  change (∑ child : Fin (branch n),
      pullback F2 (childRestriction (LeafDomain slots) child) (values child).val) =
    (H slots).subtype
      (∑ child : Fin (branch n), childSquareLift F2 (LeafDomain slots) child (values child))
  rw [map_sum]
  rfl

theorem childSquareLift_squareSum (repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (chosen : Fin (branch n))
    (values : RecursiveSampler.CallIndex repeats n → H (childSlots slots chosen)) :
    childSquareLift F2 (LeafDomain slots) chosen (squareSum repeats slots chosen values) =
      ∑ pair : Fin (repeats (n + 1)), childProduct F2 (LeafDomain slots) chosen
        (values (pair, false)) (values (pair, true)) := by
  rw [squareSum, map_sum]
  rfl

theorem recursiveSum_stepSquareMap (repeats : Nat → Nat) (chosen : Fin (branch n))
    (q : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : ScalarTape repeats chosen q slots) :
    UniformChildSum.recursiveSum (𝕜 := F2) (LeafDomain slots)
        (stepSquareMap repeats chosen q slots ω) =
      RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots) ω := by
  let ordinary : (child : RecursiveSampler.OffPath chosen) → Square slots child.val :=
    (RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω).1
  let values : RecursiveSampler.CallIndex repeats n → H (childSlots slots chosen) :=
    (RecursiveSampler.splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω).2
  have hself : stepSquareMap repeats chosen q slots ω chosen =
      squareSum repeats slots chosen values :=
    stepSquareMap_self repeats chosen q slots ω
  have hother (child : RecursiveSampler.OffPath chosen) :
      stepSquareMap repeats chosen q slots ω child.val = ordinary child :=
    stepSquareMap_other repeats chosen q slots ω child
  have heval : RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots) ω =
      (∑ child : RecursiveSampler.OffPath chosen,
        childSquareLift F2 (LeafDomain slots) child.val (ordinary child)) +
      ∑ pair : Fin (repeats (n + 1)), childProduct F2 (LeafDomain slots) chosen
        (values (pair, false)) (values (pair, true)) :=
    (RecursiveSampler.stepCombine_splitEvaluatedTape F2 repeats chosen q (LeafDomain slots) ω).symm.trans
      (RecursiveSamplerBiasAlgebra.combine_eq F2 (LeafDomain slots) chosen (repeats (n + 1))
        ordinary (fun pair => values (pair, false)) (fun pair => values (pair, true)))
  calc
    _ = ∑ child : Fin (branch n), childSquareLift F2 (LeafDomain slots) child
        (stepSquareMap repeats chosen q slots ω child) :=
      recursiveSum_eq_sum slots (stepSquareMap repeats chosen q slots ω)
    _ = childSquareLift F2 (LeafDomain slots) chosen (stepSquareMap repeats chosen q slots ω chosen) +
        ∑ child : RecursiveSampler.OffPath chosen, childSquareLift F2 (LeafDomain slots) child.val
          (stepSquareMap repeats chosen q slots ω child.val) :=
      Fintype.sum_eq_add_sum_subtype_ne _ chosen
    _ = childSquareLift F2 (LeafDomain slots) chosen (squareSum repeats slots chosen values) +
        ∑ child : RecursiveSampler.OffPath chosen,
          childSquareLift F2 (LeafDomain slots) child.val (ordinary child) :=
      congrArg₂ (fun a b : H slots => a + b)
        (congrArg (childSquareLift F2 (LeafDomain slots) chosen) hself)
        (Finset.sum_congr rfl (fun child _ =>
          congrArg (childSquareLift F2 (LeafDomain slots) child.val) (hother child)))
    _ = (∑ pair : Fin (repeats (n + 1)), childProduct F2 (LeafDomain slots) chosen
          (values (pair, false)) (values (pair, true))) +
        ∑ child : RecursiveSampler.OffPath chosen,
          childSquareLift F2 (LeafDomain slots) child.val (ordinary child) :=
      congrArg (fun z : H slots => z + ∑ child : RecursiveSampler.OffPath chosen,
        childSquareLift F2 (LeafDomain slots) child.val (ordinary child))
        (childSquareLift_squareSum repeats slots chosen values)
    _ = _ := (add_comm _ _).trans heval.symm

theorem recursiveSum_callContributions (calls : Nat) (repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : Fin calls → ScalarTape repeats chosen q slots) (call : Fin calls) :
    UniformChildSum.recursiveSum (𝕜 := F2) (LeafDomain slots)
        (fun child => callContributions calls repeats chosen q slots ω child call) =
      RecursiveSampler.evaluate F2 repeats (.step chosen q) (LeafDomain slots) (ω call) :=
  recursiveSum_stepSquareMap repeats chosen q slots (ω call)

end
end PerfectCompleteness.OriginalChildScalarAssembly


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalChildBlocks
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalChildBlocks

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalChildScalars
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem assemble_rawMap (calls : Nat) (rows repeats : Nat → Nat)
    (chosen : Fin (branch n)) (q : Path branch n m)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ω : SourceTape calls rows repeats chosen q slots) :
    CutChildGrouping.assemble slots rows (rawMap calls rows repeats chosen q slots ω) =
      observed calls rows repeats chosen q slots ω := by
  apply Prod.ext
  · funext call
    exact OriginalChildScalarAssembly.recursiveSum_callContributions
      calls repeats chosen q slots ω.1 call
  · rfl

end
end PerfectCompleteness.OriginalChildBlocks

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

theorem reconstruct_outside_eq_of_nonown_eq (rows repeats : Nat → Nat) :
    ∀ {n m : Nat} (p : Path branch n (m + 1))
      (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats p slots)
      (values₁ values₂ : Values rows repeats p slots) (below : BelowArrays rows p slots),
      (∀ call, (∀ a, call ≠ OriginalCutCalls.ownBucket rows repeats p a) →
        values₁ call = values₂ call) →
      ∀ node : Nodes branch n, node ≠ WholeArrayInteriorExterior.upperNode p →
        reconstruct rows repeats p slots exterior values₁ below node =
          reconstruct rows repeats p slots exterior values₂ below node := by
  intro n
  induction n with
  | zero => intro m p; cases p
  | succ n ih =>
      intro m p slots exterior values₁ values₂ below hvalues node hnode
      cases p with
      | refl =>
          cases node with
          | inl u => cases u; exact False.elim (hnode rfl)
          | inr pair => rfl
      | step i p =>
          have hroot : (fun direction terminal => values₁ (.inl (direction, terminal))) =
              (fun direction terminal => values₂ (.inl (direction, terminal))) := by
            funext direction terminal
            exact hvalues (.inl (direction, terminal))
              (fun a => OriginalCutCalls.root_ne_ownBucket rows repeats i p
                (direction, terminal) a)
          have hlower : ∀ call,
              (∀ a, call ≠ OriginalCutCalls.ownBucket rows repeats p a) →
              values₁ (.inr call) = values₂ (.inr call) := by
            intro call hcall
            apply hvalues (.inr call)
            intro a heq
            exact hcall a (Sum.inr.inj heq)
          cases node with
          | inl u =>
              cases u
              change reconstructBuckets rows repeats (.step i p) slots
                  (fun direction terminal => values₁ (.inl (direction, terminal))) exterior.1 =
                reconstructBuckets rows repeats (.step i p) slots
                  (fun direction terminal => values₂ (.inl (direction, terminal))) exterior.1
              rw [hroot]
          | inr pair =>
              rcases pair with ⟨child, node⟩
              by_cases hchild : child = i
              · subst child
                have hnode' : node ≠ WholeArrayInteriorExterior.upperNode p := by
                  intro h
                  exact hnode (congrArg (fun v => Sum.inr (i, v)) h)
                change WholeArraySampler.childrenAt slots rows i
                  (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                    (fun call => values₁ (.inr call)) below) exterior.2.2 i node =
                  WholeArraySampler.childrenAt slots rows i
                    (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                      (fun call => values₂ (.inr call)) below) exterior.2.2 i node
                rw [WholeArraySampler.childrenAt_selected,
                  WholeArraySampler.childrenAt_selected]
                exact ih p (childSlots slots i) exterior.2.1
                  (fun call => values₁ (.inr call)) (fun call => values₂ (.inr call))
                  below hlower node hnode'
              · change WholeArraySampler.childrenAt slots rows i
                  (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                    (fun call => values₁ (.inr call)) below) exterior.2.2 child node =
                  WholeArraySampler.childrenAt slots rows i
                    (reconstruct rows repeats p (childSlots slots i) exterior.2.1
                      (fun call => values₂ (.inr call)) below) exterior.2.2 child node
                simp only [WholeArraySampler.childrenAt, dite_eq_right hchild]

end
end PerfectCompleteness.OriginalCutBucketReplacement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_OriginalOwnBucketSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalOwnBucketSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays TerminalCalls
open OriginalWholeCut OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat}

attribute [local instance 2000] valuesChildrenFintype

theorem assembleRecord_nonown_eq (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own₁ own₂ : BucketTape rows p slots) (complement : Complement rows repeats p slots)
    (call : OriginalCutCalls.Index rows repeats p)
    (hcall : ∀ a, call ≠ OriginalCutCalls.ownBucket rows repeats p a) :
    (assembleRecord rows repeats p slots own₁ complement).2.1 call =
      (assembleRecord rows repeats p slots own₂ complement).2.1 call := by
  cases he : indexEquiv rows repeats p call with
  | inl a =>
      exfalso
      apply hcall a
      apply (indexEquiv rows repeats p).injective
      rw [indexEquiv_ownBucket]
      exact he
  | inr other =>
      have hc : call = otherCall rows repeats p other := by
        apply (indexEquiv rows repeats p).injective
        rw [indexEquiv_otherCall]
        exact he
      rw [hc, assembleRecord_other, assembleRecord_other]

theorem uniform_record_split (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
        (recordEquiv rows repeats p slots) =
      (FiniteDistribution.uniform (BucketTape rows p slots)).product
        (FiniteDistribution.uniform (Complement rows repeats p slots)) := by
  rw [← FiniteDistribution.transport_eq_pushforward,
    UniformConditioning.uniform_transport, WholeCutSampler.uniform_product]

theorem reconstruct_assembleRecord_outside (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own₁ own₂ : BucketTape rows p slots) (complement : Complement rows repeats p slots)
    (node : Nodes branch n) (hnode : node ≠ WholeArrayInteriorExterior.upperNode p) :
    reconstructRecord rows repeats p slots (assembleRecord rows repeats p slots own₁ complement)
        node =
      reconstructRecord rows repeats p slots (assembleRecord rows repeats p slots own₂ complement)
        node := by
  change reconstruct rows repeats p slots complement.1
      (assembleRecord rows repeats p slots own₁ complement).2.1 complement.2.2 node =
    reconstruct rows repeats p slots complement.1
      (assembleRecord rows repeats p slots own₂ complement).2.1 complement.2.2 node
  exact OriginalCutBucketReplacement.reconstruct_outside_eq_of_nonown_eq rows repeats p slots
    complement.1 _ _ complement.2.2
    (assembleRecord_nonown_eq rows repeats p slots own₁ own₂ complement) node hnode

theorem background_assembleRecord (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (own : BucketTape rows p slots) (complement : Complement rows repeats p slots) :
    HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
        (reconstructRecord rows repeats p slots (assembleRecord rows repeats p slots own complement)) =
      background rows repeats p slots complement := by
  funext node
  exact reconstruct_assembleRecord_outside rows repeats p slots own 0 complement node.val node.property

theorem background_record (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (record : Record rows repeats p slots) :
    HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
        (reconstructRecord rows repeats p slots record) =
      background rows repeats p slots (recordEquiv rows repeats p slots record).2 := by
  have h := background_assembleRecord rows repeats p slots
    (recordEquiv rows repeats p slots record).1 (recordEquiv rows repeats p slots record).2
  rw [assembleRecord_split] at h
  exact h

attribute [local instance] OAI.PerfectCompleteness.OriginalOwnBucketSplit.backgroundFintype
theorem uniform_own_background (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
        (fun record =>
          ((recordEquiv rows repeats p slots record).1,
            HierarchicalMatrixTable.backgroundOf slots (WholeArrayInteriorExterior.upperNode p)
              (reconstructRecord rows repeats p slots record))) =
      (FiniteDistribution.uniform (BucketTape rows p slots)).product
        (backgroundLaw rows repeats p slots) := by
  calc
    _ = ((FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
        (recordEquiv rows repeats p slots)).pushforward
          (fun z => (z.1, background rows repeats p slots z.2)) := by
      rw [FiniteDistribution.pushforward_comp]
      apply congrArg ((FiniteDistribution.uniform (Record rows repeats p slots)).pushforward)
      funext record
      exact Prod.ext rfl (background_record rows repeats p slots record)
    _ = ((FiniteDistribution.uniform (BucketTape rows p slots)).product
        (FiniteDistribution.uniform (Complement rows repeats p slots))).pushforward
          (fun z => (z.1, background rows repeats p slots z.2)) := by
      rw [uniform_record_split]
    _ = _ := by
      simpa only [id_eq, FiniteDistribution.pushforward_id, backgroundLaw] using
        (FiniteDistribution.product_pushforward
          (FiniteDistribution.uniform (BucketTape rows p slots))
          (FiniteDistribution.uniform (Complement rows repeats p slots))
          (id : BucketTape rows p slots → BucketTape rows p slots)
          (background rows repeats p slots))

end
end PerfectCompleteness.OriginalOwnBucketSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalUniformCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalUniformCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCut OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalUniformCutBase.valuesChildrenFintype

variable {branch : Nat → Nat} {n m t : Nat}

theorem referenceLaw_uniform (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    referenceLaw rows repeats p slots = FiniteDistribution.uniform (Record rows repeats p slots) := by
  unfold referenceLaw exteriorLaw
  rw [UniformLinearImage.law_uniform, UniformLinearImage.law_uniform,
    WholeCutSampler.uniform_product, WholeCutSampler.uniform_product]

end
end PerfectCompleteness.OriginalUniformCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_NumberedUniformCut
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.NumberedUniformCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

variable {branch : Nat → Nat} {n m t : Nat}

theorem reference_numberRecord_law (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    (OriginalUniformCut.referenceLaw rows repeats p slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots) =
      (exteriorLaw rows repeats p slots).product
        (FiniteDistribution.uniform (CutChildGrouping.Assembled
          (C := Fin (OriginalCutCalls.count rows repeats n (m + 1))) (cutSlots p slots) rows)) := by
  rw [OriginalUniformCut.referenceLaw_uniform]
  change (FiniteDistribution.uniform (Record rows repeats p slots)).pushforward
    (numberRecordEquiv rows repeats p slots) = _
  rw [← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  exact WholeCutSampler.uniform_product.symm

end
end PerfectCompleteness.NumberedUniformCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ExtraCutCall
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ExtraCutCall

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem product_assoc_law {E A B : Type*}
    [Fintype E] [Fintype A] [Fintype B]
    (μ : FiniteDistribution E) (ν : FiniteDistribution A) (ξ : FiniteDistribution B) :
    (μ.product (ν.product ξ)).pushforward (fun z => ((z.1, z.2.1), z.2.2)) =
      (μ.product ν).product ξ := by
  change (μ.product (ν.product ξ)).pushforward (Equiv.prodAssoc E A B).symm = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  exact (mul_assoc _ _ _).symm

private theorem lift_split_law {E D A B : Type*}
    [Fintype E] [Fintype D] [Fintype A] [Fintype B]
    (μ : FiniteDistribution E) (ν : FiniteDistribution D)
    (ρ : FiniteDistribution A) (ξ : FiniteDistribution B) (split : D → A × B)
    (hsplit : ν.pushforward split = ρ.product ξ) :
    (μ.product ν).pushforward (fun z => ((z.1, (split z.2).1), (split z.2).2)) =
      (μ.product ρ).product ξ := by
  have hmap : (μ.product ν).pushforward (fun z => (z.1, split z.2)) =
      μ.product (ρ.product ξ) := by
    have h := FiniteDistribution.product_pushforward μ ν id split
    simpa only [id_eq, FiniteDistribution.pushforward_id, hsplit] using h
  calc
    _ = ((μ.product ν).pushforward (fun z => (z.1, split z.2))).pushforward
        (fun z => ((z.1, z.2.1), z.2.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (μ.product (ρ.product ξ)).pushforward
        (fun z => ((z.1, z.2.1), z.2.2)) :=
      congrArg (fun law : FiniteDistribution (E × (A × B)) =>
        law.pushforward (fun z => ((z.1, z.2.1), z.2.2))) hmap
    _ = _ := product_assoc_law μ ρ ξ

variable {branch : Nat → Nat} {n m k t : Nat}

theorem uniform_split_law (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot) :
    (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin (calls + 1)) slots rows)).pushforward
        (splitAssembled calls rows slots) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)).product
        (FiniteDistribution.uniform (H slots)) := by
  rw [← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  exact WholeCutSampler.uniform_product.symm

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

theorem uniform_record_fresh_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ((exteriorLaw rows repeats p slots).product
      (FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (OriginalCutCalls.count rows repeats n (m + 1) + 1)) (cutSlots p slots) rows))).pushforward
        (splitRecord rows repeats p slots) =
      ((OriginalUniformCut.referenceLaw rows repeats p slots).pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product
          (FiniteDistribution.uniform (H (cutSlots p slots))) := by
  rw [NumberedUniformCut.reference_numberRecord_law]
  exact lift_split_law (exteriorLaw rows repeats p slots) _ _ _
    (splitAssembled (OriginalCutCalls.count rows repeats n (m + 1)) rows (cutSlots p slots))
    (uniform_split_law (OriginalCutCalls.count rows repeats n (m + 1)) rows (cutSlots p slots))

end
end PerfectCompleteness.ExtraCutCall

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalPrefixContinuation
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalPrefixContinuation

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n k t : Nat} {K : Type*} [Fintype K]

omit [Fintype K] in
theorem assemble_rawMap (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : K → Path branch n k) (ω : Tape calls rows repeats slots q) :
    CutChildGrouping.assemble slots rows (rawMap calls rows repeats slots q ω) =
      observed calls rows repeats slots q ω :=
  OriginalChildBlocks.assemble_rawMap calls rows repeats ω.1.1
    (q ω.1.2) slots ω.2

theorem observed_variation {Γ : Type*} [Fintype Γ]
    (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k)
    (hbranch : 0 < branch n)
    (observe : CutChildGrouping.Assembled (C := Fin calls) slots rows → Γ) :
    ((sourceLaw calls rows repeats slots ν q hbranch).pushforward
        (fun ω => observe (observed calls rows repeats slots q ω))).totalVariation
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)).pushforward
        observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        branch n) / 2 := by
  have hclean : (ChildBlockMixture.reference (Ω := fun child : Fin (branch n) =>
      ChildBlockCardinality.Raw calls rows (childSlots slots child))).pushforward
        (fun x => observe (CutChildGrouping.assemble slots rows x)) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)).pushforward
        observe := by
    rw [← FiniteDistribution.pushforward_comp]
    have h := CutChildGrouping.assemble_law (C := Fin calls) slots rows
    change (ChildBlockMixture.reference (Ω := fun child : Fin (branch n) =>
      ChildBlockCardinality.Raw calls rows (childSlots slots child))).pushforward
        (CutChildGrouping.assemble slots rows) = _ at h
    rw [h]
  have h := raw_observed_variation calls rows repeats slots ν q hbranch
    (fun x => observe (CutChildGrouping.assemble slots rows x))
  simpa only [assemble_rawMap, hclean] using h

theorem assembledLaw_variation (calls : Nat) (rows repeats : Nat → Nat)
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch n k) (hbranch : 0 < branch n) :
    (assembledLaw calls rows repeats slots ν q hbranch).totalVariation
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) slots rows)) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch n t calls rows : ℝ) ^ 2 /
        branch n) / 2 := by
  simpa only [id_eq, FiniteDistribution.pushforward_id, assembledLaw] using
    observed_variation calls rows repeats slots ν q hbranch
      (id : CutChildGrouping.Assembled (C := Fin calls) slots rows →
        CutChildGrouping.Assembled (C := Fin calls) slots rows)

end
end PerfectCompleteness.OriginalPrefixContinuation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalExtraCutComparison
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalExtraCutComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCutLaw
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {branch : Nat → Nat} {n m k t : Nat} {K : Type*} [Fintype K]

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

theorem totalVariation_le (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m) :
    (actualLaw rows repeats p slots ν q hbranch).totalVariation
      (referenceLaw rows repeats p slots) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1) + 1) rows : ℝ) ^ 2 / branch m) / 2 := by
  unfold actualLaw referenceLaw
  rw [← ExtraCutCall.uniform_record_fresh_law rows repeats p slots]
  exact CommonProductVariation.observed_product_le_of_bound
    (exteriorLaw rows repeats p slots) _ _ (ExtraCutCall.splitRecord rows repeats p slots)
    (OriginalPrefixContinuation.assembledLaw_variation
      (OriginalCutCalls.count rows repeats n (m + 1) + 1)
      rows repeats (cutSlots p slots) ν q hbranch)

theorem observed_totalVariation_le {D Γ : Type*} [Fintype D] [Fintype Γ]
    (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m)
    (directions : FiniteDistribution D) (observe : D × Record rows repeats p slots → Γ) :
    ((directions.product (actualLaw rows repeats p slots ν q hbranch)).pushforward observe).totalVariation
        ((directions.product (referenceLaw rows repeats p slots)).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1) + 1) rows : ℝ) ^ 2 / branch m) / 2 :=
  CommonProductVariation.observed_product_le_of_bound directions _ _ observe
    (totalVariation_le rows repeats p slots ν q hbranch)

end
end PerfectCompleteness.OriginalExtraCutComparison

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_OriginalCutCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutCollision

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n m k t : Nat}

attribute [local instance] OAI.PerfectCompleteness.OriginalCutCollision.backgroundFintype
local instance rowSpaceFintype_rb3d3d7_1 (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (WholeArrayInteriorExterior.upperNode p)) :=
  Fintype.ofFinite _
theorem pair_totalVariation_le {K : Type*} [Fintype K]
    (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1)))) :
    ((directions.product (OriginalExtraCutComparison.actualLaw rows repeats p slots ν q hbranch)).pushforward
      (pairRecord rows repeats p slots)).totalVariation
      ((directions.product (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
        (pairRecord rows repeats p slots)) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1) + 1) rows : ℝ) ^ 2 / branch m) / 2 :=
  OriginalExtraCutComparison.observed_totalVariation_le rows repeats p slots ν q hbranch
    directions (pairRecord rows repeats p slots)

end
end PerfectCompleteness.OriginalCutCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalCutBucketLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalCutBucketLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance 2000] OriginalWholeCutLaw.valuesBelowFintype

section Regrouping

private theorem reorder_law {D U B F : Type*}
    [Fintype D] [Fintype U] [Fintype B] [Fintype F]
    (directions : FiniteDistribution D) (own : FiniteDistribution U)
    (background : FiniteDistribution B) (fresh : FiniteDistribution F) :
    (directions.product ((own.product background).product fresh)).pushforward (reorder D U B F) =
      background.product (directions.product (own.product fresh)) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change directions.weight z.2.1 *
      ((own.weight z.2.2.1 * background.weight z.1) * fresh.weight z.2.2.2) =
    background.weight z.1 *
      (directions.weight z.2.1 * (own.weight z.2.2.1 * fresh.weight z.2.2.2))
  ring

private theorem map_middle {D R S F : Type*}
    [Fintype D] [Fintype R] [Fintype S] [Fintype F]
    (directions : FiniteDistribution D) (records : FiniteDistribution R)
    (fresh : FiniteDistribution F) (read : R → S) :
    (directions.product (records.product fresh)).pushforward
        (fun z => (z.1, (read z.2.1, z.2.2))) =
      directions.product ((records.pushforward read).product fresh) := by
  have hinner : (records.product fresh).pushforward (fun z => (read z.1, z.2)) =
      (records.pushforward read).product fresh := by
    simpa only [id_eq, FiniteDistribution.pushforward_id] using
      FiniteDistribution.product_pushforward records fresh read (id : F → F)
  calc
    _ = (directions.pushforward id).product
        ((records.product fresh).pushforward (fun z => (read z.1, z.2))) :=
      FiniteDistribution.product_pushforward directions (records.product fresh) id
        (fun z => (read z.1, z.2))
    _ = _ := by rw [FiniteDistribution.pushforward_id, hinner]

private theorem read_product_of_split {D R U B F : Type*}
    [Fintype D] [Fintype R] [Fintype U] [Fintype B] [Fintype F]
    (directions : FiniteDistribution D) (records : FiniteDistribution R)
    (fresh : FiniteDistribution F) (own : FiniteDistribution U)
    (background : FiniteDistribution B) (split : R → U × B)
    (hsplit : records.pushforward split = own.product background) :
    (directions.product (records.product fresh)).pushforward
        (fun z => ((split z.2.1).2, (z.1, ((split z.2.1).1, z.2.2)))) =
      background.product (directions.product (own.product fresh)) := by
  calc
    _ = ((directions.product (records.product fresh)).pushforward
        (fun z => (z.1, (split z.2.1, z.2.2)))).pushforward (reorder D U B F) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (directions.product ((own.product background).product fresh)).pushforward
        (reorder D U B F) := by
      rw [map_middle, hsplit]
    _ = _ := reorder_law directions own background fresh

end Regrouping

variable {branch : Nat → Nat} {n m k t : Nat}

attribute [local instance] OAI.PerfectCompleteness.OriginalCutBucketLaw.backgroundFintype
theorem read_numberRecord (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (direction : BucketSampler.Direction (rows (m + 1)))
    (record : OriginalWholeCut.Record rows repeats p slots) (fresh : H (cutSlots p slots)) :
    read rows repeats p slots
        (direction, (OriginalWholeCutBridge.numberRecord rows repeats p slots record, fresh)) =
      ((recordRead rows repeats p slots record).2,
        (direction, ((recordRead rows repeats p slots record).1, fresh))) := by
  unfold read OriginalCutCollision.oldArrays
  simp only [oldRecord_numberRecord]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · funext a
        exact (OriginalOwnBucketSplit.recordEquiv_own rows repeats p slots record a).symm
      · rfl

private theorem numbered_read_of_split (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1))))
    (records : FiniteDistribution (OriginalWholeCut.Record rows repeats p slots))
    (fresh : FiniteDistribution (H (cutSlots p slots)))
    (own : FiniteDistribution (OriginalOwnBucketSplit.BucketTape rows p slots))
    (background : FiniteDistribution (Background rows p slots))
    (hsplit : records.pushforward (recordRead rows repeats p slots) = own.product background) :
    (directions.product ((records.pushforward
        (OriginalWholeCutBridge.numberRecord rows repeats p slots)).product fresh)).pushforward
          (read rows repeats p slots) =
      background.product (directions.product (own.product fresh)) := by
  calc
    _ = (directions.product (records.product fresh)).pushforward
        (fun z => read rows repeats p slots
          (z.1, (OriginalWholeCutBridge.numberRecord rows repeats p slots z.2.1, z.2.2))) := by
      rw [← map_middle directions records fresh
        (OriginalWholeCutBridge.numberRecord rows repeats p slots),
        FiniteDistribution.pushforward_comp]
    _ = (directions.product (records.product fresh)).pushforward
        (fun z => ((recordRead rows repeats p slots z.2.1).2,
          (z.1, ((recordRead rows repeats p slots z.2.1).1, z.2.2)))) := by
      apply congrArg (directions.product (records.product fresh)).pushforward
      funext z
      exact read_numberRecord rows repeats p slots z.1 z.2.1 z.2.2
    _ = _ := read_product_of_split directions records fresh own background
      (recordRead rows repeats p slots) hsplit

theorem reference_read_law (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1)))) :
    (directions.product (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
        (read rows repeats p slots) =
      (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots).product
        (directions.product
          ((FiniteDistribution.uniform (OriginalOwnBucketSplit.BucketTape rows p slots)).product
            (FiniteDistribution.uniform (H (cutSlots p slots))))) := by
  unfold OriginalExtraCutComparison.referenceLaw
  rw [OriginalUniformCut.referenceLaw_uniform]
  exact numbered_read_of_split rows repeats p slots directions
    (FiniteDistribution.uniform (OriginalWholeCut.Record rows repeats p slots))
    (FiniteDistribution.uniform (H (cutSlots p slots)))
    (FiniteDistribution.uniform (OriginalOwnBucketSplit.BucketTape rows p slots))
    (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
    (OriginalOwnBucketSplit.uniform_own_background rows repeats p slots)

end
end PerfectCompleteness.OriginalCutBucketLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OriginalCutPairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
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

private theorem transportPair_law (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (μ : FiniteDistribution (HierarchicalMatrixTable.Background (rows := rows) slots (upperNode p)))
    (ν : FiniteDistribution (BucketSampler.Direction (rows (m + 1)) ×
      (BucketSampler.Tape (rows (m + 1)) (H (cutSlots p slots)) × H (cutSlots p slots)))) :
    (μ.product ν).pushforward (transportPair rows p slots) =
      ((μ.product ν).pushforward
        (fun z : OriginalCutBucketLaw.NativeSample rows p slots =>
          (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))).pushforward
        (HierarchicalAgreementMean.pairRecord slots (upperNode p)) := by
  exact (FiniteDistribution.pushforward_comp (μ.product ν)
    (fun z : OriginalCutBucketLaw.NativeSample rows p slots =>
      (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))
    (HierarchicalAgreementMean.pairRecord slots (upperNode p))).symm

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

theorem reference_pair_law (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (hrows : 0 < rows (m + 1)) :
    ((directionsLaw rows m hrows).product
      (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
        (OriginalCutCollision.pairRecord rows repeats p slots) =
      HierarchicalAgreementMean.referenceLaw slots (upperNode p)
        (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
        (by simpa only [upperNode_height] using hrows) := by
  let μ := OriginalOwnBucketSplit.backgroundLaw rows repeats p slots
  have hread := OriginalCutBucketLaw.reference_read_law rows repeats p slots
    (directionsLaw rows m hrows)
  have hnative :
      ((directionsLaw rows m hrows).product
        (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
          (OriginalCutBucketLaw.read rows repeats p slots) =
        μ.product (CutBucketTransport.nativeLaw rows p slots hrows) := by
    simpa only [μ, CutBucketTransport.nativeLaw, directionsLaw,
      BucketSampler.tapeLaw, UniformLinearImage.law_uniform] using hread
  have htransport := FiniteDistribution.product_pushforward μ
    (CutBucketTransport.nativeLaw rows p slots hrows) id
    (CutNodeRows.bucketSampleEquiv rows p slots)
  simp only [id_eq, FiniteDistribution.pushforward_id] at htransport
  calc
    _ = (((directionsLaw rows m hrows).product
        (OriginalExtraCutComparison.referenceLaw rows repeats p slots)).pushforward
          (OriginalCutBucketLaw.read rows repeats p slots)).pushforward
            (transportPair rows p slots) := by
      rw [FiniteDistribution.pushforward_comp]
      congr 1
      funext sample
      exact pairRecord_eq rows repeats p slots sample
    _ = (μ.product (CutBucketTransport.nativeLaw rows p slots hrows)).pushforward
        (transportPair rows p slots) := by rw [hnative]
    _ = ((μ.product (CutBucketTransport.nativeLaw rows p slots hrows)).pushforward
        (fun z => (z.1, CutNodeRows.bucketSampleEquiv rows p slots z.2))).pushforward
          (HierarchicalAgreementMean.pairRecord slots (upperNode p)) :=
      transportPair_law rows p slots μ (CutBucketTransport.nativeLaw rows p slots hrows)
    _ = _ := by
      rw [htransport, CutBucketTransport.nativeLaw_pushforward]
      rfl

theorem actual_pair_totalVariation_le_oai {K : Type*} [Fintype K]
    (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (ν : FiniteDistribution K) (q : K → Path branch m k) (hbranch : 0 < branch m)
    (hrows : 0 < rows (m + 1)) :
    (((directionsLaw rows m hrows).product
      (OriginalExtraCutComparison.actualLaw rows repeats p slots ν q hbranch)).pushforward
        (OriginalCutCollision.pairRecord rows repeats p slots)).totalVariation
      (HierarchicalAgreementMean.referenceLaw slots (upperNode p)
        (OriginalOwnBucketSplit.backgroundLaw rows repeats p slots)
        (by simpa only [upperNode_height] using hrows)) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1) + 1) rows : ℝ) ^ 2 / branch m) / 2 := by
  rw [← reference_pair_law rows repeats p slots hrows]
  exact OriginalCutCollision.pair_totalVariation_le rows repeats p slots ν q hbranch
    (directionsLaw rows m hrows)

end
end PerfectCompleteness.OriginalCutPairLaw

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PerfectCompleteness.OriginalCutPairLaw.actual_pair_totalVariation_le_oai.{u_1} := @OAI.PerfectCompleteness.OriginalCutPairLaw.actual_pair_totalVariation_le_oai.{u_1}
