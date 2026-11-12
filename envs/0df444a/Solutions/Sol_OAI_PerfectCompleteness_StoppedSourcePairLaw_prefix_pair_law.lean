-- Prove2me | solution 1 for OAI.PerfectCompleteness.StoppedSourcePairLaw.prefix_pair_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:27:41.757531+00:00
-- url     : https://prove2.me/submissions/69e9cb0f-ecd3-4f26-8996-35d4fff027cc

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
import Definitions.Def_OAIQ252P020
import Theorems.Thm_OAI_PerfectCompleteness_UpperScalarCutProjection_fixed_projected_law

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

end
end PerfectCompleteness.FiniteProduct

end

end OAI
end

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
-- module Solutions.OAIQ252_PC.UniqueGames_Games_CompletedSamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
# Finite local completion after correlated sampling

One independent seed contains the original shared seed and two full response
tables. Its local reads give exactly the mixture of the requested completion
kernels. Applying those kernels contracts total variation. On a diagonal
target the same construction uses one common selected label.
-/

namespace UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

open scoped BigOperators
open Games

noncomputable section

section DistributionIdentities

variable {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

theorem mixture_pushforward_base (μ : FiniteDistribution A) (f : A → B)
    (K : B → FiniteDistribution C) :
    (μ.pushforward f).mixture K = μ.mixture (fun a => K (f a)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro c
  exact FiniteDistribution.expectation_pushforward μ f (fun b => (K b).weight c)

end DistributionIdentities

end

end UniqueGamesTheorem.Foundations.Repetition.CompletedSampling

end

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_MultiplicationFormInjectiveLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.MarkedKernelProduct

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

variable {Z : I → Type*} [∀ i, Fintype (Z i)]

theorem law_mixture (ρ : (i : I) → FiniteDistribution (Z i))
    (Q : (i : I) → Z i → FiniteDistribution (Ω i)) :
    FiniteProduct.law (fun i => (ρ i).mixture (Q i)) =
      (FiniteProduct.law ρ).mixture
        (fun z => FiniteProduct.law (fun i => Q i (z i))) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ i, (ρ i).expectation (fun z => (Q i z).weight (x i))) =
    (FiniteProduct.law ρ).expectation (fun z => ∏ i, (Q i (z i)).weight (x i))
  exact (FiniteProduct.expectation_product ρ (fun i z => (Q i z).weight (x i))).symm

end
end PerfectCompleteness.MarkedKernelProduct


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ChildAssemblyProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildAssemblyProjection

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}

theorem recursiveSum_pullback
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (f : (i : Fin (branch n)) → squareSpace (H (childSlots projected i))) :
    UniformChildSum.recursiveSum (LeafDomain slots)
        (fun i => ChildBlockProjection.squarePullback (childProjection p i) (f i)) =
      HPullback p (UniformChildSum.recursiveSum (LeafDomain projected) f) := by
  apply Subtype.ext
  change (∑ i, PointwiseSpaces.pullback F2 (childRestriction (LeafDomain slots) i)
      (ChildBlockProjection.squarePullback (childProjection p i) (f i)).val) =
    PointwiseSpaces.pullback F2 (sourceProjection p)
      (∑ i, PointwiseSpaces.pullback F2 (childRestriction (LeafDomain projected) i) (f i).val)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

variable {C : Type*} [Fintype C]

omit [Fintype C] in
theorem assemble_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (block : CutChildGrouping.Raw (C := C) projected rows) :
    CutChildGrouping.assemble slots rows (rawPullback rows p block) =
      assembledPullback rows p (CutChildGrouping.assemble projected rows block) := by
  apply Prod.ext
  · funext call
    exact recursiveSum_pullback p (fun i => (block i).1 call)
  · rfl

theorem pushforward_assemble (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (μ : FiniteDistribution (CutChildGrouping.Raw (C := C) projected rows)) :
    (μ.pushforward (rawPullback rows p)).pushforward (CutChildGrouping.assemble slots rows) =
      (μ.pushforward (CutChildGrouping.assemble projected rows)).pushforward
        (assembledPullback rows p) := by
  rw [FiniteDistribution.pushforward_comp, FiniteDistribution.pushforward_comp]
  congr 1
  funext block
  exact assemble_pullback rows p block

theorem uniform_projected_assembly (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k)) :
    ((CutChildGrouping.rawLaw (C := C) projected rows).pushforward
        (rawPullback rows p)).pushforward (CutChildGrouping.assemble slots rows) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := C) projected rows)).pushforward
        (assembledPullback rows p) := by
  rw [pushforward_assemble, CutChildGrouping.assemble_law]

end
end PerfectCompleteness.ChildAssemblyProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionPositionSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
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

theorem tree_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildQuestionLaw.assembleEquiv designated (join designated q positions) =
      fun leaf k => (q leaf k, positions leaf k) :=
  (SourceChildQuestionLaw.assembleEquiv (m := m) (t := t) designated).apply_symm_apply _

theorem child_tree_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t))
    (i : Fin (branch n)) (leaf : Slots branch n) (k : Fin t) :
    SourceChildKernel.tree designated i (join designated q positions i) leaf k =
      (q (i, leaf) k, positions (i, leaf) k) :=
  congrFun (congrFun (tree_join designated q positions) (i, leaf)) k

end
end PerfectCompleteness.SourceQuestionPositionSplit

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
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedCutChoices
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedCutChoices

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem mixture_const {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) :
    μ.mixture (fun _ => ν) = ν := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∑ a, μ.weight a * ν.weight x) = ν.weight x
  rw [← Finset.sum_mul, μ.normalized, one_mul]

private theorem product_mixture {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (P : A × B → FiniteDistribution C) :
    (μ.product ν).mixture P = μ.mixture (fun a => ν.mixture (fun b => P (a, b))) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  simp only [FiniteDistribution.mixture,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

private theorem lifted_keep {branch : Nat → Nat} {n t : Nat}
    (calls : Nat) (rows : Nat → Nat)
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    ChildBlockProjection.liftedLaw calls rows (fun s a => MixedSupport.Projection.keep (slots s a)) =
      FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows slots) := by
  unfold ChildBlockProjection.liftedLaw
  have hmap : (ChildBlockProjection.rawPullback calls rows
      (fun s a => MixedSupport.Projection.keep (slots s a)) :
      ChildBlockCardinality.Raw calls rows slots → ChildBlockCardinality.Raw calls rows slots) = id := by
    funext block
    apply Prod.ext
    · funext call
      apply Subtype.ext
      funext x
      rfl
    · funext node row
      apply Subtype.ext
      funext x
      rfl
  rw [hmap, FiniteDistribution.pushforward_id]

variable {branch : Nat → Nat} {n t : Nat}
  {Z : Fin (branch n) → Type*} [∀ child, Fintype (Z child)]
  (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (projected : (child : Fin (branch n)) → Z child → Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots slots child s a) (projected child z s a))

theorem row_eq_mixture (calls : Nat) (rows : Nat → Nat)
    (choiceLaw : (child : Fin (branch n)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) (child : Fin (branch n)) :
    SparseReplacement.row
      (fun child => FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (childSlots slots child)))
      (ChildBlockProjection.replacementLaws calls rows (fun child => childSlots slots child)
        projected projection choiceLaw) β hβ hβ' child =
      ((ProjectionPosterior.bernoulli β hβ hβ').product (choiceLaw child)).mixture
        (childLaw slots projected projection calls rows child) := by
  rw [product_mixture]
  unfold SparseReplacement.row
  apply congrArg ((ProjectionPosterior.bernoulli β hβ hβ').mixture)
  funext flag
  cases flag with
  | false =>
      simp only [Bool.false_eq_true, ite_false, if_false]
      change FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (childSlots slots child)) =
        (choiceLaw child).mixture (fun z => ChildBlockProjection.liftedLaw calls rows
          (fun s a => MixedSupport.Projection.keep (childSlots slots child s a)))
      simp only [lifted_keep, mixture_const]
  | true => rfl

theorem raw_eq_mixture (calls : Nat) (rows : Nat → Nat)
    (choiceLaw : (child : Fin (branch n)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    SparseReplacement.law
      (fun child => FiniteDistribution.uniform (ChildBlockCardinality.Raw calls rows (childSlots slots child)))
      (ChildBlockProjection.replacementLaws calls rows (fun child => childSlots slots child)
        projected projection choiceLaw) β hβ hβ' =
      (choicesLaw choiceLaw β hβ hβ').mixture (fun choices =>
        FiniteProduct.law (fun child => childLaw slots projected projection calls rows child (choices child))) := by
  unfold SparseReplacement.law
  have hrow := funext (row_eq_mixture slots projected projection calls rows choiceLaw β hβ hβ')
  rw [hrow]
  exact MarkedKernelProduct.law_mixture
    (fun child => (ProjectionPosterior.bernoulli β hβ hβ').product (choiceLaw child))
    (childLaw slots projected projection calls rows)

omit [(child : Fin (branch n)) → Fintype (Z child)] in
theorem fixed_assembly (calls : Nat) (rows : Nat → Nat) (choices : Choices (Z := Z)) :
    (FiniteProduct.law (fun child =>
      childLaw slots projected projection calls rows child (choices child))).pushforward
        (CutChildGrouping.assemble slots rows) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls)
        (selectedSlots slots projected choices) rows)).pushforward
          (ChildAssemblyProjection.assembledPullback rows
            (selectedProjection slots projected projection choices)) := by
  have hraw : (CutChildGrouping.rawLaw (C := Fin calls)
      (selectedSlots slots projected choices) rows).pushforward
        (ChildAssemblyProjection.rawPullback rows (selectedProjection slots projected projection choices)) =
      FiniteProduct.law (fun child =>
        childLaw slots projected projection calls rows child (choices child)) := by
    exact FiniteProduct.pushforward_map
      (fun child => FiniteDistribution.uniform (CutChildGrouping.Child (C := Fin calls)
        (selectedSlots slots projected choices) rows child))
      (fun child => ChildAssemblyProjection.childPullback rows
        (selectedProjection slots projected projection choices) child)
  rw [← hraw]
  exact ChildAssemblyProjection.uniform_projected_assembly rows
    (selectedProjection slots projected projection choices)

theorem assembled_eq_mixture (calls : Nat) (rows : Nat → Nat)
    (choiceLaw : (child : Fin (branch n)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    ProjectedPrefixComparison.assembledLaw calls rows slots projected projection choiceLaw β hβ hβ' =
      (choicesLaw choiceLaw β hβ hβ').mixture (fun choices =>
        (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls)
          (selectedSlots slots projected choices) rows)).pushforward
            (ChildAssemblyProjection.assembledPullback rows
              (selectedProjection slots projected projection choices))) := by
  unfold ProjectedPrefixComparison.assembledLaw
  rw [raw_eq_mixture slots projected projection calls rows choiceLaw β hβ hβ',
    FiniteDistribution.pushforward_mixture]
  apply congrArg ((choicesLaw choiceLaw β hβ hβ').mixture)
  funext choices
  exact fixed_assembly slots projected projection calls rows choices

end
end PerfectCompleteness.ProjectedCutChoices

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedWholeCut
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedWholeCut

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m j t : Nat}
  (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  {Z : Fin (branch m) → Type*} [∀ child, Fintype (Z child)]
  (projected : (child : Fin (branch m)) → Z child → Slots branch m → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots (cutSlots p slots) child s a) (projected child z s a))

omit [∀ child, Fintype (Z child)] in
theorem cut_fullSlots (choices : ProjectedCutChoices.Choices (Z := Z)) :
    cutSlots p (fullSlots p slots projected choices) =
      ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices := by
  funext s a
  exact congrFun (CutSlotAssembly.fill_at_cut p slots
    (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices) s) a

omit [∀ child, Fintype (Z child)] in
theorem cut_fullProjection (choices : ProjectedCutChoices.Choices (Z := Z))
    (s : Slots branch (m + 1)) (a : Fin t) :
    HEq (CutGroupedProjection.cutProjection p (fullProjection p slots projected projection choices) s a)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices s a) :=
  (CutProjectionAssembly.castProjection_heq
    (congrFun (congrFun (fill_native p slots) (p.slotEmbedding s)) a) rfl
    (CutProjectionAssembly.fillProjection p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices)
      (p.slotEmbedding s) a)).trans
    (CutProjectionAssembly.fillProjection_at_cut p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices) s a)

omit [∀ child, Fintype (Z child)] in
theorem fullSlots_outside (choices : ProjectedCutChoices.Choices (Z := Z))
    (s : Slots branch n) (hs : WholeCutExteriorTransport.Outside p s) :
    slots s = fullSlots p slots projected choices s := by
  calc
    slots s = CutSlotAssembly.fill p slots (cutSlots p slots) s :=
      (congrFun (fill_native p slots) s).symm
    _ = _ := CutSlotAssembly.fill_outside_eq p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices) s hs

omit [∀ child, Fintype (Z child)] in
theorem fullProjection_outside (choices : ProjectedCutChoices.Choices (Z := Z))
    (s : Slots branch n) (hs : WholeCutExteriorTransport.Outside p s) (a : Fin t) :
    HEq (fullProjection p slots projected projection choices s a)
      (MixedSupport.Projection.keep (slots s a)) := by
  have hkeep : HEq
      (MixedSupport.Projection.keep (CutSlotAssembly.fill p slots (cutSlots p slots) s a))
      (MixedSupport.Projection.keep (slots s a)) := by
    rw [fill_native p slots]
  exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
    ((CutProjectionGeometry.fillProjection_outside p slots (cutSlots p slots)
      (ProjectedCutChoices.selectedSlots (cutSlots p slots) projected choices)
      (ProjectedCutChoices.selectedProjection (cutSlots p slots) projected projection choices) s hs a).trans
        hkeep)

end
end PerfectCompleteness.ProjectedWholeCut

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ProjectedUpperPair
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedUpperPair

noncomputable section

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

attribute [local instance] linearMapFintype

private theorem product_mixture_right {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (P : B → FiniteDistribution C) :
    μ.product (ν.mixture P) = ν.mixture (fun b => μ.product (P b)) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change μ.weight x.1 * (∑ b, ν.weight b * (P b).weight x.2) =
    ∑ b, ν.weight b * (μ.weight x.1 * (P b).weight x.2)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

private theorem lifted_assembled_congr {branch : Nat → Nat} {m t : Nat}
    (calls : Nat) (rows : Nat → Nat)
    (left right right' : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (q' : ∀ s a, MixedSupport.Projection (left s a) (right' s a))
    (hright : right = right') (hq : ∀ s a, HEq (q s a) (q' s a)) :
    (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) right rows)).pushforward
      (ChildAssemblyProjection.assembledPullback rows q) =
    (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := Fin calls) right' rows)).pushforward
      (ChildAssemblyProjection.assembledPullback rows q') := by
  cases hright
  have heq : q = q' := by
    funext s a
    exact eq_of_heq (hq s a)
  cases heq
  rfl

variable {branch : Nat → Nat} {n j i t : Nat}

variable (p : Path branch n (j + 1)) (r : Path branch (j + 1) (i + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  {Z : Fin (branch i) → Type*} [∀ child, Fintype (Z child)]
  (projected : (child : Fin (branch i)) → Z child → Slots branch i → Fin t → MixedSupport.Slot)
  (projection : ∀ child z s a, MixedSupport.Projection
    (childSlots (cutSlots (p.append r) slots) child s a) (projected child z s a))

attribute [local instance] OAI.PerfectCompleteness.ProjectedUpperPair.backgroundFintype
local instance rowSpaceFintype_rd75a1a_1 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
omit [∀ child, Fintype (Z child)] in
theorem fixed_law (rows repeats : Nat → Nat) (hproper : i + 1 < j + 1)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (choices : ProjectedCutChoices.Choices (Z := Z)) :
    UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      ((FiniteDistribution.uniform (CutChildGrouping.Assembled
        (C := Fin (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)))
        (ProjectedCutChoices.selectedSlots (cutSlots (p.append r) slots) projected choices) rows)).pushforward
          (ChildAssemblyProjection.assembledPullback rows
            (ProjectedCutChoices.selectedProjection (cutSlots (p.append r) slots)
              projected projection choices))) =
      (directions.product
        ((WholeArraySampler.tapeLaw rows repeats (p.append r)
          (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)).product
          (RecursiveSampler.law F2 repeats r
            (LeafDomain (cutSlots p
              (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)))))).pushforward
        (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r hproper slots
          (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)
          (ProjectedWholeCut.fullProjection (p.append r) slots projected projection choices)) := by
  have h := UpperScalarCutProjection.fixed_projected_law rows repeats p r hproper slots
    (ProjectedWholeCut.fullSlots (p.append r) slots projected choices)
    (ProjectedWholeCut.fullProjection (p.append r) slots projected projection choices)
    (ProjectedWholeCut.fullSlots_outside (p.append r) slots projected choices)
    (ProjectedWholeCut.fullProjection_outside (p.append r) slots projected projection choices)
    directions
  have hblocks := lifted_assembled_congr
    (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
    (cutSlots (p.append r) slots)
    (cutSlots (p.append r) (ProjectedWholeCut.fullSlots (p.append r) slots projected choices))
    (ProjectedCutChoices.selectedSlots (cutSlots (p.append r) slots) projected choices)
    (CutGroupedProjection.cutProjection (p.append r)
      (ProjectedWholeCut.fullProjection (p.append r) slots projected projection choices))
    (ProjectedCutChoices.selectedProjection (cutSlots (p.append r) slots) projected projection choices)
    (ProjectedWholeCut.cut_fullSlots (p.append r) slots projected choices)
    (ProjectedWholeCut.cut_fullProjection (p.append r) slots projected projection choices)
  rw [hblocks] at h
  exact h

theorem reconstruct_assembled_law (rows repeats : Nat → Nat) (hproper : i + 1 < j + 1)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1))))
    (choiceLaw : (child : Fin (branch i)) → FiniteDistribution (Z child))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    UpperScalarPairComparison.pairLaw rows repeats p r slots directions
      (ProjectedPrefixComparison.assembledLaw
        (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
        (cutSlots (p.append r) slots) projected projection choiceLaw β hβ hβ') =
      pairLaw p r slots projected projection rows repeats hproper directions choiceLaw β hβ hβ' := by
  unfold UpperScalarPairComparison.pairLaw
  rw [ProjectedCutChoices.assembled_eq_mixture (cutSlots (p.append r) slots) projected projection
    (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows choiceLaw β hβ hβ',
    product_mixture_right, product_mixture_right, FiniteDistribution.pushforward_mixture]
  unfold pairLaw
  apply congrArg ((ProjectedCutChoices.choicesLaw choiceLaw β hβ hβ').mixture)
  funext choices
  exact fixed_law p r slots projected projection rows repeats hproper directions choices

end
end PerfectCompleteness.ProjectedUpperPair

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SlotProjectedExperiment
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SlotProjectedExperiment

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

variable (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (pref : GeometricCutSplit.Prefix branch n (j + 1))

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

section Source

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch i) → Slots branch i)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := i) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
  (flags : SourceProjectedTag.Flags (branch := branch) (n := i))

private theorem tree_sources (leaf : Slots branch (i + 1)) (a : Fin t) :
    SourceChildKernel.tree designated leaf.1
      (SourceQuestionKernelJoint.sources designated q choices leaf.1) leaf.2 a =
      (q leaf a, choices leaf.1 leaf.2 a) := by
  rcases leaf with ⟨child, tail⟩
  have h := SourceQuestionPositionSplit.child_tree_join designated q
    (SourceQuestionPositionSplit.byChild.symm choices) child tail a
  change SourceChildKernel.tree designated child
    (SourceQuestionKernelJoint.sources designated q choices child) tail a =
      (q (child, tail) a, choices child tail a) at h
  exact h

theorem mixedInside_source :
    mixedInside (SourceProjectedTag.originalSlots clauses q) choices flags =
      SourceProjectedTag.mixedInside clauses designated q choices flags := by
  funext leaf a
  have htree := tree_sources designated q choices leaf a
  cases hf : flags leaf.1 <;>
    simp only [mixedInside, flaggedSlot, selectSlot, SourceProjectedTag.mixedInside,
      SourceProjectedTag.originalSlots, sourceSlots, PreliminarySampler.endpoints,
      SourceChildKernel.mixedSlots, SourceChildKernel.nativeSlots,
      ProjectedCardinality.projectedSlots, SourceChildKernel.ids,
      SourceClause.occurrenceVariable, SourceKeys.slot, hf, htree]

private theorem projection_family_heq
    {left right₁ right₂ : Slots branch (i + 1) → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (p₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hp : ∀ leaf a, HEq (p₁ leaf a) (p₂ leaf a)) : HEq p₁ p₂ := by
  subst right₂
  apply heq_of_eq
  funext leaf a
  exact eq_of_heq (hp leaf a)

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private theorem flagged_occurrence_heq
    {e e' : SourceClause.Occurrence m} (h : e = e') (b : Bool) :
    HEq (flaggedProjection (SourceKeys.slot clauses (.clause e.1)) e.2 b)
      (flaggedProjection (SourceKeys.slot clauses (.clause e'.1)) e'.2 b) := by
  cases h
  rfl

private theorem child_projection_as_flagged (child : Fin (branch i))
    (s : SourceChildKernel.Source (m := m) (t := t) designated child)
    (b : Bool) (leaf : Slots branch i) (a : Fin t) :
    HEq (SourceChildKernel.projection clauses designated child s b leaf a)
      (flaggedProjection
        (SourceKeys.slot clauses (.clause (SourceChildKernel.tree designated child s leaf a).1))
        (SourceChildKernel.tree designated child s leaf a).2 b) := by
  cases b <;> rfl

theorem insideProjection_source :
    HEq (insideProjection (SourceProjectedTag.originalSlots clauses q) choices flags)
      (SourceProjectedTag.projection clauses designated q choices flags) := by
  apply projection_family_heq (mixedInside_source clauses designated q choices flags)
  intro leaf a
  have htree := tree_sources designated q choices leaf a
  have hcast : HEq (SourceProjectedTag.projection clauses designated q choices flags leaf a)
      (SourceChildKernel.projection clauses designated leaf.1
        (SourceQuestionKernelJoint.sources designated q choices leaf.1)
        (flags leaf.1) leaf.2 a) := by
    unfold SourceProjectedTag.projection
    dsimp only [id]
    exact mpr_heq _ _
  have hflagged := flagged_occurrence_heq clauses htree.symm (flags leaf.1)
  have hchild := child_projection_as_flagged clauses designated leaf.1
    (SourceQuestionKernelJoint.sources designated q choices leaf.1)
    (flags leaf.1) leaf.2 a
  exact hflagged.trans (hchild.symm.trans hcast.symm)

end Source

end
end PerfectCompleteness.SlotProjectedExperiment

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceProjectedChoices
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedChoices

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t m v : Nat}

theorem tagEquiv_law (flag : Fin (branch n) → FiniteDistribution Bool) :
    (FiniteProduct.law (fun child =>
      (flag child).product (choiceLaw (t := t) child))).pushforward
        (tagEquiv (branch := branch) (n := n) (t := t)) =
      SourceProjectedTag.law (t := t) flag := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro tag
  change (∏ child : Fin (branch n), (flag child).weight (tag.2 child) *
      (choiceLaw (t := t) child).weight (tag.1 child)) =
    (∏ child : Fin (branch n), (choiceLaw (t := t) child).weight (tag.1 child)) *
      ∏ child : Fin (branch n), (flag child).weight (tag.2 child)
  rw [Finset.prod_mul_distrib, mul_comm]

theorem choicesLaw_tagEquiv (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (ProjectedCutChoices.choicesLaw
      (choiceLaw (branch := branch) (n := n) (t := t)) β hβ hβ').pushforward
        (tagEquiv (branch := branch) (n := n) (t := t)) =
      SourceProjectedTag.law (t := t)
        (fun _ : Fin (branch n) => ProjectionPosterior.bernoulli β hβ hβ') :=
  tagEquiv_law (t := t) (fun _ => ProjectionPosterior.bernoulli β hβ hβ')

theorem tagLaw_choices (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    (SourceProjectedTag.law (t := t)
      (fun _ : Fin (branch n) => ProjectionPosterior.bernoulli β hβ hβ')).pushforward
        (tagEquiv (branch := branch) (n := n) (t := t)).symm =
      ProjectedCutChoices.choicesLaw
        (choiceLaw (branch := branch) (n := n) (t := t)) β hβ hβ' := by
  rw [← choicesLaw_tagEquiv β hβ hβ', FiniteDistribution.pushforward_comp]
  simp only [Equiv.symm_apply_apply]
  exact FiniteDistribution.pushforward_id _

variable (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)

theorem childDomain_eq (child : Fin (branch n)) (flag : Bool)
    (positions : Positions (branch := branch) (n := n) (t := t))
    (leaf : Slots branch n) (a : Fin t) :
    ProjectedCutChoices.childDomain slots (projected slots) child (flag, positions) leaf a =
      SlotProjectedExperiment.flaggedSlot (slots (child, leaf) a) (positions leaf a) flag := by
  cases flag <;> rfl

theorem childProjection_heq (child : Fin (branch n)) (flag : Bool)
    (positions : Positions (branch := branch) (n := n) (t := t))
    (leaf : Slots branch n) (a : Fin t) :
    HEq (ProjectedCutChoices.childProjection slots (projected slots) (projection slots)
      child (flag, positions) leaf a)
      (SlotProjectedExperiment.flaggedProjection
        (slots (child, leaf) a) (positions leaf a) flag) := by
  cases flag <;> rfl

theorem selectedSlots_tag
    (tag : SourceProjectedTag.Tag (branch := branch) (n := n) (t := t)) :
    ProjectedCutChoices.selectedSlots slots (projected slots) (tagEquiv.symm tag) =
      SlotProjectedExperiment.mixedInside slots tag.1 tag.2 := by
  funext leaf a
  exact childDomain_eq slots leaf.1 (tag.2 leaf.1) (tag.1 leaf.1) leaf.2 a

private theorem projection_family_heq
    {left right₁ right₂ : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (p₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hp : ∀ leaf a, HEq (p₁ leaf a) (p₂ leaf a)) : HEq p₁ p₂ := by
  subst right₂
  apply heq_of_eq
  funext leaf a
  exact eq_of_heq (hp leaf a)

theorem selectedProjection_tag
    (tag : SourceProjectedTag.Tag (branch := branch) (n := n) (t := t)) :
    HEq (ProjectedCutChoices.selectedProjection slots (projected slots) (projection slots)
      (tagEquiv.symm tag))
      (SlotProjectedExperiment.insideProjection slots tag.1 tag.2) := by
  apply projection_family_heq (selectedSlots_tag slots tag)
  intro leaf a
  exact childProjection_heq slots leaf.1 (tag.2 leaf.1) (tag.1 leaf.1) leaf.2 a

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)
  (questions : SourceQuestionPositionSplit.Questions
    (branch := branch) (n := n) (t := t) (m := m))

theorem selectedSlots_source
    (tag : SourceProjectedTag.Tag (branch := branch) (n := n) (t := t)) :
    ProjectedCutChoices.selectedSlots (SourceProjectedTag.originalSlots clauses questions)
      (projected (SourceProjectedTag.originalSlots clauses questions)) (tagEquiv.symm tag) =
      SourceProjectedTag.mixedInside clauses designated questions tag.1 tag.2 :=
  (selectedSlots_tag (SourceProjectedTag.originalSlots clauses questions) tag).trans
    (SlotProjectedExperiment.mixedInside_source clauses designated questions tag.1 tag.2)

theorem selectedProjection_source
    (tag : SourceProjectedTag.Tag (branch := branch) (n := n) (t := t)) :
    HEq (ProjectedCutChoices.selectedProjection
      (SourceProjectedTag.originalSlots clauses questions)
      (projected (SourceProjectedTag.originalSlots clauses questions))
      (projection (SourceProjectedTag.originalSlots clauses questions)) (tagEquiv.symm tag))
      (SourceProjectedTag.projection clauses designated questions tag.1 tag.2) :=
  (selectedProjection_tag (SourceProjectedTag.originalSlots clauses questions) tag).trans
    (SlotProjectedExperiment.insideProjection_source clauses designated questions tag.1 tag.2)

end
end PerfectCompleteness.SourceProjectedChoices

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceProjectedWholeChoices
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceProjectedWholeChoices

noncomputable section

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))
  (lowerPref : GeometricCutSplit.Prefix branch (j + 1) (i + 1))

private theorem filled_projection_heq (p : Path branch n (i + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right₁ right₂ : Slots branch (i + 1) → Fin t → MixedSupport.Slot)
    (hleft : CutSlotAssembly.fill p outside left = outside) (hr : right₁ = right₂)
    (q₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (q₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hq : HEq q₁ q₂) :
    HEq (fun leaf a => CutProjectionAssembly.castProjection
        (congrFun (congrFun hleft leaf) a) rfl
        (CutProjectionAssembly.fillProjection p outside left right₁ q₁ leaf a))
      (fun leaf a => CutProjectionAssembly.castProjection
        (congrFun (congrFun hleft leaf) a) rfl
        (CutProjectionAssembly.fillProjection p outside left right₂ q₂ leaf a)) := by
  subst right₂
  have hq' : q₁ = q₂ := eq_of_heq hq
  subst q₂
  rfl

theorem fullSlots_eq
    (choices : SourceProjectedChoices.Choices (branch := branch) (n := i) (t := t)) :
    ProjectedWholeCut.fullSlots (path hupper hij o lowerPref)
        (StoppedProjectedExperiment.nativeSlots clauses o)
        (projected clauses hupper hij o lowerPref) choices =
      StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
        (StoppedProjectedBucketIndex.key rows hrows
          (lowerPref, SourceProjectedChoices.tagEquiv choices)) := by
  have hinside := SourceProjectedChoices.selectedSlots_source clauses designated
    (StoppedProjectedExperiment.cutQuestions rows hupper hij o
      (StoppedProjectedBucketIndex.key rows hrows
        (lowerPref, SourceProjectedChoices.tagEquiv choices)))
    (SourceProjectedChoices.tagEquiv choices)
  simp only [Equiv.symm_apply_apply] at hinside
  exact congrArg (CutSlotAssembly.fill (path hupper hij o lowerPref)
    (StoppedProjectedExperiment.nativeSlots clauses o)) hinside

theorem fullProjection_heq
    (choices : SourceProjectedChoices.Choices (branch := branch) (n := i) (t := t)) :
    HEq (ProjectedWholeCut.fullProjection (path hupper hij o lowerPref)
        (StoppedProjectedExperiment.nativeSlots clauses o)
        (projected clauses hupper hij o lowerPref)
        (projection clauses hupper hij o lowerPref) choices)
      (StoppedProjectedExperiment.projection clauses rows hupper hij designated o
        (StoppedProjectedBucketIndex.key rows hrows
          (lowerPref, SourceProjectedChoices.tagEquiv choices))) := by
  have hinside := SourceProjectedChoices.selectedSlots_source clauses designated
    (StoppedProjectedExperiment.cutQuestions rows hupper hij o
      (StoppedProjectedBucketIndex.key rows hrows
        (lowerPref, SourceProjectedChoices.tagEquiv choices)))
    (SourceProjectedChoices.tagEquiv choices)
  have hprojection := SourceProjectedChoices.selectedProjection_source clauses designated
    (StoppedProjectedExperiment.cutQuestions rows hupper hij o
      (StoppedProjectedBucketIndex.key rows hrows
        (lowerPref, SourceProjectedChoices.tagEquiv choices)))
    (SourceProjectedChoices.tagEquiv choices)
  simp only [Equiv.symm_apply_apply] at hinside hprojection
  exact filled_projection_heq (path hupper hij o lowerPref)
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (nativeCutSlots clauses hupper hij o lowerPref) _ _
    (ProjectedWholeCut.fill_native (path hupper hij o lowerPref)
      (StoppedProjectedExperiment.nativeSlots clauses o))
    hinside _ _ hprojection

end
end PerfectCompleteness.SourceProjectedWholeChoices

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

attribute [local instance] OAI.PerfectCompleteness.StoppedSourcePairLaw.backgroundFintype
local instance rowSpaceFintype_rd75a1a_2 (p : Path branch n (j + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) :
    Fintype (NodeEmbedding.RowSpace slots (upperNode p)) := Fintype.ofFinite _
private theorem pair_law_congr (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1)) (hproper : i + 1 < j + 1)
    (native right right' : Slots branch n → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (projection' : ∀ s a, MixedSupport.Projection (native s a) (right' s a))
    (hright : right = right') (hprojection : HEq projection projection')
    (directions : FiniteDistribution (BucketSampler.Direction (rows (j + 1)))) :
    (directions.product ((WholeArraySampler.tapeLaw rows repeats (p.append r) right).product
      (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p right))))).pushforward
        (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r hproper native right projection) =
    (directions.product ((WholeArraySampler.tapeLaw rows repeats (p.append r) right').product
      (RecursiveSampler.law F2 repeats r (LeafDomain (cutSlots p right'))))).pushforward
        (UpperScalarCutProjection.stoppedProjectedPair rows repeats p r hproper native right' projection') := by
  subst right'
  have hprojection' : projection = projection' := eq_of_heq hprojection
  subst projection'
  rfl

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)
  (hrows : ∀ k, 0 < rows (k + 1))
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))

local instance nativeBackgroundFintype_rd75a1a_1 :
    Fintype (HierarchicalAgreementMean.Background (rows := rows)
      (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _
local instance nativeRowSpaceFintype_rd75a1a_1 :
    Fintype (NodeEmbedding.RowSpace (StoppedProjectedExperiment.nativeSlots clauses o)
      (StoppedProjectedExperiment.upper hupper o)) :=
  Fintype.ofFinite _
theorem fixed_choice_pair
    (lowerPref : GeometricCutSplit.Prefix branch (j + 1) (i + 1))
    (choices : SourceProjectedChoices.Choices (branch := branch) (n := i) (t := t)) :
    ((OriginalCutPairLaw.directionsLaw rows j (hrows j)).product
      ((WholeArraySampler.tapeLaw rows repeats
        ((StoppedProjectedExperiment.upperPath hupper o).append
          (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
        (ProjectedWholeCut.fullSlots
          ((StoppedProjectedExperiment.upperPath hupper o).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
          (StoppedProjectedExperiment.nativeSlots clauses o)
          (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref) choices)).product
        (RecursiveSampler.law F2 repeats
          (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref)
          (LeafDomain (cutSlots (StoppedProjectedExperiment.upperPath hupper o)
            (ProjectedWholeCut.fullSlots
              ((StoppedProjectedExperiment.upperPath hupper o).append
                (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
              (StoppedProjectedExperiment.nativeSlots clauses o)
              (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref) choices)))))).pushforward
      (UpperScalarCutProjection.stoppedProjectedPair rows repeats
        (StoppedProjectedExperiment.upperPath hupper o)
        (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref)
        (Nat.succ_lt_succ hij) (StoppedProjectedExperiment.nativeSlots clauses o)
        (ProjectedWholeCut.fullSlots
          ((StoppedProjectedExperiment.upperPath hupper o).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
          (StoppedProjectedExperiment.nativeSlots clauses o)
          (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref) choices)
        (ProjectedWholeCut.fullProjection
          ((StoppedProjectedExperiment.upperPath hupper o).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
          (StoppedProjectedExperiment.nativeSlots clauses o)
          (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref)
          (SourceProjectedWholeChoices.projection clauses hupper hij o lowerPref) choices)) =
      StoppedProjectedPairMean.fixedPair clauses rows repeats hupper hij designated hrows o
        (lowerPref, SourceProjectedChoices.tagEquiv choices) := by
  exact pair_law_congr rows repeats (StoppedProjectedExperiment.upperPath hupper o)
    (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref) (Nat.succ_lt_succ hij)
    (StoppedProjectedExperiment.nativeSlots clauses o) _ _ _ _
    (SourceProjectedWholeChoices.fullSlots_eq clauses rows hupper hij designated hrows o lowerPref choices)
    (SourceProjectedWholeChoices.fullProjection_heq clauses rows hupper hij designated hrows o lowerPref choices)
    (OriginalCutPairLaw.directionsLaw rows j (hrows j))

theorem prefix_pair_law_oai
    (lowerPref : GeometricCutSplit.Prefix branch (j + 1) (i + 1))
    (β : ℝ) (hβ : 0 ≤ β) (hβ' : β ≤ 1) :
    UpperScalarPairComparison.pairLaw rows repeats (StoppedProjectedExperiment.upperPath hupper o)
        (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref)
        (StoppedProjectedExperiment.nativeSlots clauses o)
        (OriginalCutPairLaw.directionsLaw rows j (hrows j))
        (ProjectedPrefixComparison.assembledLaw
          (UpperScalarCutCalls.count rows repeats n (j + 1) (i + 1)) rows
          (cutSlots ((StoppedProjectedExperiment.upperPath hupper o).append
            (GeometricCutSplit.prefixPath (Nat.succ_le_succ hij.le) lowerPref))
            (StoppedProjectedExperiment.nativeSlots clauses o))
          (SourceProjectedWholeChoices.projected clauses hupper hij o lowerPref)
          (SourceProjectedWholeChoices.projection clauses hupper hij o lowerPref)
          (SourceProjectedChoices.choiceLaw (t := t)) β hβ hβ') =
      (SourceProjectedTag.law (t := t)
        (fun _ : Fin (branch i) => ProjectionPosterior.bernoulli β hβ hβ')).mixture
          (fun tag => StoppedProjectedPairMean.fixedPair clauses rows repeats hupper hij
            designated hrows o (lowerPref, tag)) := by
  rw [ProjectedUpperPair.reconstruct_assembled_law _ _ _ _ _ rows repeats
    (Nat.succ_lt_succ hij)]
  unfold ProjectedUpperPair.pairLaw
  rw [← SourceProjectedChoices.tagLaw_choices β hβ hβ',
    UniqueGamesTheorem.Foundations.Repetition.CompletedSampling.mixture_pushforward_base]
  apply congrArg ((SourceProjectedTag.law (t := t)
    (fun _ : Fin (branch i) => ProjectionPosterior.bernoulli β hβ hβ')).mixture)
  funext tag
  simpa only [Equiv.apply_symm_apply] using
    fixed_choice_pair clauses rows repeats hupper hij designated hrows o lowerPref
      (SourceProjectedChoices.tagEquiv.symm tag)

end
end PerfectCompleteness.StoppedSourcePairLaw

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.StoppedSourcePairLaw.prefix_pair_law_oai := @OAI.PerfectCompleteness.StoppedSourcePairLaw.prefix_pair_law_oai
