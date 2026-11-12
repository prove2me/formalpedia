-- Prove2me | solution 1 for OAI.PerfectCompleteness.LowerCutPairBackground.arraysPair_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:57.904811+00:00
-- url     : https://prove2.me/submissions/6d747607-a317-4d39-9204-3842215964c2

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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Disjoint
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
import Definitions.Def_OAIQ252P017

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_UniformLinearImage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformChildSum
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerLocality
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSamplerLocality

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces
open CutSamplerRefinement

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem evaluate_step (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A) :
    CutSamplerRefinement.evaluate 𝕜 repeats (.step i p) A tape =
      RecursiveSampler.combine 𝕜 A i (repeats (n + 1))
        (fun j => tape (Sum.inl j))
        (fun h => CutSamplerRefinement.evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A tape h false))
        (fun h => CutSamplerRefinement.evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A tape h true)) := rfl

end
end PerfectCompleteness.CutSamplerLocality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutTerminalZero
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutTerminalZero

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls
open scoped Classical

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}
  (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)

theorem splitTape_terminal_step (i : Fin (branch n))
    (p : Path branch n (m + 1)) (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) (terminal : TerminalIndex repeats p) :
    (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).1 ((h, b), terminal) =
      (CutTerminalSplit.splitTape 𝕜 repeats p (childFamily A i)
        (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).1 terminal := by
  simp only [CutTerminalSplit.splitTape_terminal_apply]
  rfl

end
end PerfectCompleteness.CutTerminalZero

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerKeyLocalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.CutSamplerReplayGrouping

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem subExterior_splitTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    subExterior 𝕜 repeats i p A (h, b)
        (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).2 =
      (CutTerminalSplit.splitTape 𝕜 repeats p (childFamily A i)
        (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).2 := by
  funext j
  rfl

end
end PerfectCompleteness.CutSamplerReplayGrouping

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformDifference
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UniformDifference

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

variable {B H : Type*} [Fintype B] [Fintype H] [AddGroup H]

theorem expectation_difference (μ : FiniteDistribution B) (old : B → H)
    (f : B × H → ℝ) :
    (μ.product (FiniteDistribution.uniform H)).expectation
        (fun p => f (difference old p)) =
      (μ.product (FiniteDistribution.uniform H)).expectation f := by
  rw [FiniteDistribution.expectation_product, FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro b
  rw [FiniteDistribution.expectation_uniform, FiniteDistribution.expectation_uniform]
  simpa only [Fintype.expect_eq_sum_div_card, difference, sub_eq_add_neg] using
    Fintype.expect_equiv (Equiv.addRight (-old b))
      (fun h : H => f (b, h - old b)) (fun h : H => f (b, h))
      (fun _ => by simp only [sub_eq_add_neg]; rfl)

theorem difference_law (μ : FiniteDistribution B) (old : B → H) :
    (μ.product (FiniteDistribution.uniform H)).pushforward (difference old) =
      μ.product (FiniteDistribution.uniform H) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  have h := expectation_difference μ old (fun p => if p = z then (1 : ℝ) else 0)
  rw [← FiniteDistribution.expectation_pushforward
    (μ.product (FiniteDistribution.uniform H)) (difference old)
    (fun p => if p = z then (1 : ℝ) else 0)] at h
  simpa only [FiniteDistribution.expectation, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true] using h

end
end PerfectCompleteness.UniformDifference

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerDirectionFiber
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerDirectionFiber

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction)

variable {ℓ : Nat}

variable {H : Type*} [AddCommGroup H] [Module F2 H]

theorem replace_eq (a : Direction ℓ) (S : Rows H ℓ) (fresh : H) :
    replace a S fresh = S + BucketSampler.rankOne a.val (fresh - S (pivot a)) := by
  funext i
  by_cases hi : i = pivot a
  · subst i
    simp only [replace, restore_pivot, Pi.add_apply, BucketSampler.rankOne,
      pivot_value, one_smul]
    abel
  · simp only [replace, restore, dite_eq_right hi, complement, Pi.add_apply,
      BucketSampler.rankOne, smul_sub]
    abel

section ActualFunctions

variable {X : Type*} (V : Submodule F2 (X → F2))

theorem ofRows_add_rankOne (a : Direction ℓ) (S : Rows V ℓ) (h : V) :
    EvaluationMatrix.ofRows V (S + BucketSampler.rankOne a.val h) =
      EvaluationMatrix.shift V (EvaluationMatrix.ofRows V S) a.val h := by
  apply LinearMap.ext
  intro q
  funext i
  change q (S i + a.val i • h) = q (S i) + q h * a.val i
  simp only [map_add, map_smul, smul_eq_mul, mul_comm]

end ActualFunctions

section Laws

variable [Fintype H]

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change (1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card B : ℝ)) =
    1 / (Fintype.card (A × B) : ℝ)
  simp only [Fintype.card_prod, Nat.cast_mul, one_div, mul_inv]

theorem two_copy_law (a : Direction ℓ) :
    ((FiniteDistribution.uniform (Rows H ℓ)).product (FiniteDistribution.uniform H)).pushforward
      (fun z => (z.1, replace a z.1 z.2)) = fiberPairLaw (H := H) a := by
  have h :
      ((FiniteDistribution.uniform (Rows H ℓ)).product (FiniteDistribution.uniform H)).pushforward
        (pairCoordinates a) =
      (FiniteDistribution.uniform (Complement a H)).product
        ((FiniteDistribution.uniform H).product (FiniteDistribution.uniform H)) := by
    rw [uniform_product, uniform_product, uniform_product,
      ← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  have h' := congrArg
    (fun μ : FiniteDistribution (Complement a H × (H × H)) => μ.pushforward
      (fun z => (restore a z.1 z.2.1, restore a z.1 z.2.2))) h
  rw [FiniteDistribution.pushforward_comp] at h'
  simpa only [pairCoordinates_apply, restore_complement, replace, fiberPairLaw] using h'

theorem resampled_pair_law (μ : FiniteDistribution (Rows H ℓ)) (a : Direction ℓ) :
    (μ.product (FiniteDistribution.uniform H)).pushforward
      (fun z => (z.1, replace a z.1 z.2)) =
    (μ.product (FiniteDistribution.uniform H)).pushforward
      (fun z => (z.1, z.1 + BucketSampler.rankOne a.val z.2)) := by
  have h := congrArg
    (fun ν : FiniteDistribution (Rows H ℓ × H) => ν.pushforward
      (fun z => (z.1, z.1 + BucketSampler.rankOne a.val z.2)))
    (UniformDifference.difference_law μ (fun S => S (pivot a)))
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [UniformDifference.difference, replace_eq] using h

theorem fiberPairLaw_eq_rankOne (a : Direction ℓ) :
    fiberPairLaw (H := H) a =
      ((FiniteDistribution.uniform (Rows H ℓ)).product (FiniteDistribution.uniform H)).pushforward
        (fun z => (z.1, z.1 + BucketSampler.rankOne a.val z.2)) := by
  rw [← two_copy_law]
  exact resampled_pair_law (FiniteDistribution.uniform (Rows H ℓ)) a

end Laws

section MatrixLaws

variable {X : Type*} (V : Submodule F2 (X → F2))
  [FiniteDimensional F2 V] [Fintype V]
  [Fintype (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2))]

theorem matrix_pair_law (a : Direction ℓ) :
    (fiberPairLaw (H := V) a).pushforward
        (fun z => (EvaluationMatrix.ofRows V z.1, EvaluationMatrix.ofRows V z.2)) =
      ((FiniteDistribution.uniform (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2))).product
        (FiniteDistribution.uniform V)).pushforward
          (fun z => (z.1, EvaluationMatrix.shift V z.1 a.val z.2)) := by
  have hprod :
      ((FiniteDistribution.uniform (Rows V ℓ)).product (FiniteDistribution.uniform V)).pushforward
          (fun z => (EvaluationMatrix.ofRows V z.1, z.2)) =
        (FiniteDistribution.uniform (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2))).product
          (FiniteDistribution.uniform V) := by
    rw [uniform_product, uniform_product]
    change (FiniteDistribution.uniform (Rows V ℓ × V)).pushforward
      (Equiv.prodCongr (EvaluationMatrix.rowsEquiv V).symm (Equiv.refl V)) = _
    rw [← FiniteDistribution.transport_eq_pushforward, UniformConditioning.uniform_transport]
  have h := congrArg
    (fun μ : FiniteDistribution ((Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2)) × V) =>
      μ.pushforward (fun z => (z.1, EvaluationMatrix.shift V z.1 a.val z.2))) hprod
  rw [FiniteDistribution.pushforward_comp] at h
  rw [fiberPairLaw_eq_rankOne, FiniteDistribution.pushforward_comp]
  simpa only [ofRows_add_rankOne] using h

end MatrixLaws
end
end PerfectCompleteness.LowerDirectionFiber

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeArrayInteriorExteriorLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutCalls.card_refl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.TerminalCalls.card_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_refl _root_.OAI.PerfectCompleteness.TerminalCalls.drawIndex_step _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_recursive _root_.OAI.PerfectCompleteness.TerminalCalls.isTerminal_refl _root_.OAI.PerfectCompleteness.TerminalCalls.not_isTerminal_ordinary _root_.OAI.PerfectCompleteness.TerminalCalls.terminalSubtypeEquiv_apply _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutCalls.card_refl _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SelectedArrayReplacement

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem replace_step (rows : Nat → Nat) (i : Fin (branch n)) (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots (.step i p) slots)) :
    replace rows (.step i p) slots arrays fresh =
      WholeArraySampler.assemble slots rows (arrays (.inl ()))
        (WholeArraySampler.childrenAt slots rows i
          (replace rows p (childSlots slots i) (fun node => arrays (.inr (i, node))) fresh)
          (fun child node => arrays (.inr (child.val, node)))) := rfl

@[simp] theorem replace_assemble_step (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (root : Fin (rows (n + 1)) → H slots) (selected : Arrays (childSlots slots i) rows)
    (ordinary : ∀ child : RecursiveSampler.OffPath i, Arrays (childSlots slots child.val) rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots (.step i p) slots)) :
    replace rows (.step i p) slots
        (WholeArraySampler.assemble slots rows root
          (WholeArraySampler.childrenAt slots rows i selected ordinary)) fresh =
      WholeArraySampler.assemble slots rows root
        (WholeArraySampler.childrenAt slots rows i
          (replace rows p (childSlots slots i) selected fresh) ordinary) := by
  simp only [replace_step, WholeArraySampler.assemble,
    WholeArraySampler.childrenAt_selected, WholeArraySampler.childrenAt_ordinary]

theorem replace_outside (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
      (fresh : Fin (rows (m + 1)) → H (subtreeSlots p slots)) (node : Nodes branch n),
      node ≠ upperNode p → replace rows p slots arrays fresh node = arrays node := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro slots arrays fresh node hnode
          cases node with
          | inl u => cases u; exact False.elim (hnode rfl)
          | inr pair => rfl
      | step i p =>
          intro slots arrays fresh node hnode
          cases node with
          | inl u => cases u; rfl
          | inr pair =>
              rcases pair with ⟨child, node⟩
              by_cases hchild : child = i
              · subst child
                have hnode' : node ≠ upperNode p := by
                  intro h
                  exact hnode (congrArg (fun v => Sum.inr (i, v)) h)
                exact (congrFun (WholeArraySampler.childrenAt_selected slots rows i
                  (replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh)
                  (fun j v => arrays (.inr (j.val, v)))) node).trans
                    (ih p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh node hnode')
              · exact congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
                    (replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh)
                    (fun j v => arrays (.inr (j.val, v))) ⟨child, hchild⟩) node

@[simp] theorem replace_same (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows),
      replace rows p slots arrays (selectedRows rows p slots arrays) = arrays := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro slots arrays
          funext node
          rcases node with u | ⟨child, node⟩
          · cases u
            rfl
          · rfl
      | step i p =>
          intro slots arrays
          rw [replace_step, selectedRows_step,
            ih p (childSlots slots i) (fun v => arrays (.inr (i, v)))]
          funext node
          rcases node with u | ⟨child, node⟩
          · cases u
            rfl
          · by_cases hchild : child = i
            · subst child
              exact congrFun (WholeArraySampler.childrenAt_selected slots rows i
                (fun v => arrays (.inr (i, v))) (fun j v => arrays (.inr (j.val, v)))) node
            · exact congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
                (fun v => arrays (.inr (i, v))) (fun j v => arrays (.inr (j.val, v)))
                ⟨child, hchild⟩) node

end
end PerfectCompleteness.SelectedArrayReplacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutNodeCoordinates
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutNodeCoordinates

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem rowEquiv_selectedRows (rows : Nat → Nat) :
    {n m : Nat} → (p : Path branch n (m + 1)) →
      (slots : Slots branch n → Fin t → MixedSupport.Slot) →
      (arrays : Arrays slots rows) →
      rowEquiv rows p slots (SelectedArrayReplacement.selectedRows rows p slots arrays) =
        arrays (upperNode p)
  | _, _, .refl _, _, _ => rfl
  | _, _, .step i p, slots, arrays =>
      rowEquiv_selectedRows rows p (childSlots slots i) (fun node => arrays (.inr (i, node)))

theorem replace_eq_update (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (arrays : Arrays slots rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots p slots)) :
    SelectedArrayReplacement.replace rows p slots arrays fresh =
      Function.update arrays (upperNode p) (rowEquiv rows p slots fresh) := by
  funext node
  by_cases hnode : node = upperNode p
  · subst node
    rw [Function.update_self]
    have h := rowEquiv_selectedRows rows p slots
      (SelectedArrayReplacement.replace rows p slots arrays fresh)
    rw [SelectedArrayReplacement.selectedRows_replace] at h
    exact h.symm
  · rw [Function.update_of_ne hnode]
    exact SelectedArrayReplacement.replace_outside rows p slots arrays fresh node hnode

end
end PerfectCompleteness.LowerCutNodeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutScalar
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutScalar

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem reconstruct_step (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u)
    (values : Values 𝕜 repeats (.step i p) A)
    (exterior : CutTerminalSplit.ExteriorTape 𝕜 repeats (.step i p) A) :
    reconstruct 𝕜 repeats (.step i p) A values exterior =
      RecursiveSampler.combine 𝕜 A i (repeats (n + 1))
        (fun j => exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩)
        (fun h => reconstruct 𝕜 repeats p (childFamily A i)
          (fun terminal => values ((h, false), terminal))
          (CutSamplerReplayGrouping.subExterior 𝕜 repeats i p A (h, false) exterior))
        (fun h => reconstruct 𝕜 repeats p (childFamily A i)
          (fun terminal => values ((h, true), terminal))
          (CutSamplerReplayGrouping.subExterior 𝕜 repeats i p A (h, true) exterior)) := rfl

theorem reconstruct_splitTape (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      reconstruct 𝕜 repeats p A
          (fun terminal => UniformChildSum.recursiveSum (p.family A)
            ((CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal))
          (CutTerminalSplit.splitTape 𝕜 repeats p A tape).2 =
        CutSamplerRefinement.evaluate 𝕜 repeats p A tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A tape
          rfl
      | step i p =>
          intro A tape
          rw [reconstruct_step, CutSamplerLocality.evaluate_step]
          apply congrArg₂ (RecursiveSampler.combine 𝕜 A i (repeats (n + 1))
            (fun j => tape (.inl j)))
          · funext h
            rw [CutSamplerReplayGrouping.subExterior_splitTape]
            simp_rw [CutTerminalZero.splitTape_terminal_step]
            exact ih p (childFamily A i)
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h false)
          · funext h
            rw [CutSamplerReplayGrouping.subExterior_splitTape]
            simp_rw [CutTerminalZero.splitTape_terminal_step]
            exact ih p (childFamily A i)
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h true)

end
end PerfectCompleteness.LowerCutScalar

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_WholeCutSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutRowsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem selectedRows_evaluate_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots) :
    SelectedArrayReplacement.selectedRows rows (.step i p) slots
        (WholeCutSampler.evaluate rows repeats (.step i p) slots tape) =
      SelectedArrayReplacement.selectedRows rows p (childSlots slots i)
        (WholeCutSampler.evaluate rows repeats p (childSlots slots i) tape.2.1) := by
  rw [SelectedArrayReplacement.selectedRows_step]
  apply congrArg (SelectedArrayReplacement.selectedRows rows p (childSlots slots i))
  funext node
  unfold WholeCutSampler.evaluate
  rw [WholeArraySampler.evaluate_selected]
  rfl

theorem selectedRows_evaluate (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeCutSampler.Tape rows repeats p slots) (row : Fin (rows (m + 1))),
      SelectedArrayReplacement.selectedRows rows p slots
          (WholeCutSampler.evaluate rows repeats p slots tape) row =
        (CutChildGrouping.assemble (cutSlots p slots) rows
          ((splitTape rows repeats p slots tape).2)).1
            (WholeCutCalls.directRow rows repeats p row) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots tape row; rfl
      | step i p =>
          intro slots tape row
          rw [selectedRows_evaluate_step]
          exact ih p (childSlots slots i) tape.2.1 row

theorem selectedRows_reconstruct (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) (row : Fin (rows (m + 1))) :
    SelectedArrayReplacement.selectedRows rows p slots
        (reconstruct rows repeats p slots exterior raw) row =
      (CutChildGrouping.assemble (cutSlots p slots) rows raw).1
        (WholeCutCalls.directRow rows repeats p row) := by
  unfold reconstruct
  rw [selectedRows_evaluate, Equiv.apply_symm_apply]

theorem selectedRows_reconstruct_eq (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) :
    SelectedArrayReplacement.selectedRows rows p slots
        (reconstruct rows repeats p slots exterior raw) =
      selectRows rows repeats p slots
        (CutChildGrouping.assemble (cutSlots p slots) rows raw) := by
  funext row
  exact selectedRows_reconstruct rows repeats p slots exterior raw row

end
end PerfectCompleteness.LowerCutRows

end

section

namespace PerfectCompleteness.LowerCutAssembled

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem reconstruct_splitTape (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeCutSampler.Tape rows repeats p slots),
      reconstruct rows repeats p slots (splitTape rows repeats p slots tape).1
          (CutChildGrouping.assemble (cutSlots p slots) rows
            (splitTape rows repeats p slots tape).2) =
        WholeCutSampler.evaluate rows repeats p slots tape := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots tape; rfl
      | step i p =>
          intro slots tape
          apply congrArg₂ (WholeArraySampler.assemble slots rows)
          · apply congrArg (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots))
            funext direction
            exact LowerCutScalar.reconstruct_splitTape F2 repeats (.step i p)
              (LeafDomain slots) (tape.1 direction)
          · exact congrArg (fun selected : Arrays (childSlots slots i) rows =>
              WholeArraySampler.childrenAt slots rows i selected tape.2.2)
              (ih p (childSlots slots i) tape.2.1)

theorem reconstruct_assemble (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) :
    reconstruct rows repeats p slots exterior
        (CutChildGrouping.assemble (cutSlots p slots) rows raw) =
      LowerCutRows.reconstruct rows repeats p slots exterior raw := by
  have h := reconstruct_splitTape rows repeats p slots
    ((splitTape rows repeats p slots).symm (exterior, raw))
  rw [Equiv.apply_symm_apply] at h
  exact h

theorem reconstruct_congr_replace (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (exterior : Exterior rows repeats p slots)
      (x y : Assembled rows repeats p slots),
      (∀ call, (∀ row, call ≠ WholeCutCalls.directRow rows repeats p row) →
        y.1 call = x.1 call) → y.2 = x.2 →
      reconstruct rows repeats p slots exterior y =
        SelectedArrayReplacement.replace rows p slots
          (reconstruct rows repeats p slots exterior x)
          (LowerCutRows.selectRows rows repeats p slots y) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro slots exterior x y hcalls harrays
          change WholeArraySampler.assemble slots rows y.1 y.2 =
            WholeArraySampler.assemble slots rows y.1 x.2
          rw [harrays]
      | step i p =>
          intro slots exterior x y hcalls harrays
          simp only [reconstruct, SelectedArrayReplacement.replace_assemble_step]
          apply congrArg₂ (WholeArraySampler.assemble slots rows)
          · unfold reconstructBuckets
            apply congrArg (BucketSampler.evaluate (rows (n + 1)) (id : H slots → H slots))
            funext direction
            apply congrArg (fun values => LowerCutScalar.reconstruct F2 repeats (.step i p)
              (LeafDomain slots) values (exterior.1 direction))
            funext terminal
            apply hcalls (.inl (direction, terminal))
            intro row h
            cases h
          · apply congrArg (fun selected : Arrays (childSlots slots i) rows =>
              WholeArraySampler.childrenAt slots rows i selected exterior.2.2)
            apply ih p (childSlots slots i) exterior.2.1
              (fun call => x.1 (.inr call), x.2)
              (fun call => y.1 (.inr call), y.2)
            · intro call hcall
              apply hcalls (.inr call)
              intro row h
              exact hcall row (Sum.inr.inj h)
            · exact harrays

end
end PerfectCompleteness.LowerCutAssembled

end

section

namespace PerfectCompleteness.LowerCutCallSplit

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)

theorem splitAssembled_surjective : Function.Surjective (splitAssembled rows repeats p slots) :=
  (splitEquiv rows repeats p slots).surjective

end
end PerfectCompleteness.LowerCutCallSplit

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CutCallExtension
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutCallExtension

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  (slots : RecursiveSpaces.Slots branch (n + 1) → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat)

omit [Fintype C] in
theorem splitAssembled_surjective : Function.Surjective
    (splitAssembled (C := C) slots rows) := by
  rintro ⟨⟨old, arrays⟩, extra⟩
  refine ⟨(fun c => match c with | none => extra | some c => old c, arrays), ?_⟩
  rfl

theorem observe_law :
    (CutChildGrouping.rawLaw (C := Option C) slots rows).pushforward
        (observe slots rows) =
      (FiniteDistribution.uniform (CutChildGrouping.Assembled (C := C) slots rows)).product
        (FiniteDistribution.uniform (H slots)) := by
  change (CutChildGrouping.rawLaw (C := Option C) slots rows).pushforward
    (fun x => splitAssembled slots rows (CutChildGrouping.assemble slots rows x)) = _
  rw [← FiniteDistribution.pushforward_comp, CutChildGrouping.assemble_law,
    UniformLinearImage.uniform_pushforward_linearMap
      (splitAssembled slots rows) (splitAssembled_surjective slots rows)]
  exact WholeCutSampler.uniform_product.symm

end
end PerfectCompleteness.CutCallExtension

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairBackground
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutPairBackground

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

theorem splitObservation_surjective :
    Function.Surjective (splitObservation rows repeats p slots) := by
  rintro ⟨c, S, h⟩
  obtain ⟨record, hrecord⟩ :=
    LowerCutCallSplit.splitAssembled_surjective rows repeats p slots (c, S)
  refine ⟨(record, h), ?_⟩
  change ((LowerCutCallSplit.splitAssembled rows repeats p slots record).1,
    ((LowerCutCallSplit.splitAssembled rows repeats p slots record).2, h)) = (c, S, h)
  rw [hrecord]

theorem observe_law :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (cutSlots p slots) rows).pushforward (observe rows repeats p slots) =
      (FiniteDistribution.uniform (Complement rows repeats p slots)).product
        ((FiniteDistribution.uniform (NativeRows rows p slots)).product
          (FiniteDistribution.uniform (H (cutSlots p slots)))) := by
  change (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
    (cutSlots p slots) rows).pushforward
      (fun raw => splitObservation rows repeats p slots
        (CutCallExtension.observe (cutSlots p slots) rows raw)) = _
  rw [← FiniteDistribution.pushforward_comp, CutCallExtension.observe_law,
    WholeCutSampler.uniform_product,
    UniformLinearImage.uniform_pushforward_linearMap
      (splitObservation rows repeats p slots) (splitObservation_surjective rows repeats p slots)]
  rw [WholeCutSampler.uniform_product, WholeCutSampler.uniform_product]

@[simp] theorem observe_rows (exterior : Exterior rows repeats p slots)
    (raw : LowerCutPair.Raw rows repeats p slots) :
    (observe rows repeats p slots raw).2.1 =
      SelectedArrayReplacement.selectedRows rows p slots
        (LowerCutPair.first rows repeats p slots exterior raw) := by
  exact (LowerCutRows.selectedRows_reconstruct_eq rows repeats p slots exterior _).symm

theorem rowPair_law (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (cutSlots p slots) rows).pushforward (rowPair rows repeats p slots exterior a) =
      (FiniteDistribution.uniform (Complement rows repeats p slots)).product
        (LowerDirectionFiber.fiberPairLaw (H := H (cutSlots p slots)) a) := by
  have h := congrArg
    (fun μ : FiniteDistribution (Observation rows repeats p slots) => μ.pushforward
      (fun z => (z.1, (z.2.1, LowerDirectionFiber.replace a z.2.1 z.2.2))))
    (observe_law rows repeats p slots)
  rw [FiniteDistribution.pushforward_comp] at h
  have hp := FiniteDistribution.product_pushforward
      (FiniteDistribution.uniform (Complement rows repeats p slots))
      ((FiniteDistribution.uniform (NativeRows rows p slots)).product
        (FiniteDistribution.uniform (H (cutSlots p slots))))
      (id : Complement rows repeats p slots → Complement rows repeats p slots)
      (fun z => (z.1, LowerDirectionFiber.replace a z.1 z.2))
  simp only [FiniteDistribution.pushforward_id, id_eq, LowerDirectionFiber.two_copy_law] at hp
  have hfinal := h.trans hp
  change (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
    (cutSlots p slots) rows).pushforward (fun raw =>
      ((observe rows repeats p slots raw).1,
        (SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.first rows repeats p slots exterior raw),
         SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.second rows repeats p slots exterior a raw)))) = _
  simpa only [LowerCutPair.selected_second,
    observe_rows rows repeats p slots exterior, observe_fresh] using hfinal

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

theorem matrixPair_law (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (cutSlots p slots) rows).pushforward (matrixPair rows repeats p slots exterior a) =
      (FiniteDistribution.uniform (Complement rows repeats p slots)).product
        (((FiniteDistribution.uniform (NativeMatrix rows p slots)).product
          (FiniteDistribution.uniform (H (cutSlots p slots)))).pushforward
            (fun z => (z.1, EvaluationMatrix.shift (H (cutSlots p slots)) z.1 a.val z.2))) := by
  have h := congrArg
    (fun μ : FiniteDistribution
      (Complement rows repeats p slots × (NativeRows rows p slots × NativeRows rows p slots)) =>
      μ.pushforward (fun z => (z.1,
        (EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2.1,
          EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2.2))))
    (rowPair_law rows repeats p slots exterior a)
  rw [FiniteDistribution.pushforward_comp] at h
  have hp := FiniteDistribution.product_pushforward
      (FiniteDistribution.uniform (Complement rows repeats p slots))
      (LowerDirectionFiber.fiberPairLaw (H := H (cutSlots p slots)) a)
      (id : Complement rows repeats p slots → Complement rows repeats p slots)
      (fun z => (EvaluationMatrix.ofRows (H (cutSlots p slots)) z.1,
        EvaluationMatrix.ofRows (H (cutSlots p slots)) z.2))
  simp only [FiniteDistribution.pushforward_id, id_eq, LowerDirectionFiber.matrix_pair_law] at hp
  exact h.trans hp

theorem reconstruct_merge (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (S : NativeRows rows p slots) :
    LowerCutAssembled.reconstruct rows repeats p slots exterior
        (LowerCutCallSplit.merge rows repeats p slots c S) =
      installRows rows repeats p slots exterior c S := by
  have h := LowerCutAssembled.reconstruct_congr_replace rows repeats p slots exterior
    (LowerCutCallSplit.merge rows repeats p slots c 0)
    (LowerCutCallSplit.merge rows repeats p slots c S)
    (fun call hcall =>
      (LowerCutCallSplit.merge_otherCall rows repeats p slots c S ⟨call, hcall⟩).trans
        (LowerCutCallSplit.merge_otherCall rows repeats p slots c 0 ⟨call, hcall⟩).symm) rfl
  rw [LowerCutCallSplit.selectRows_merge] at h
  exact h

theorem first_eq_installRows (exterior : Exterior rows repeats p slots)
    (raw : LowerCutPair.Raw rows repeats p slots) :
    LowerCutPair.first rows repeats p slots exterior raw =
      installRows rows repeats p slots exterior (observe rows repeats p slots raw).1
        (SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.first rows repeats p slots exterior raw)) := by
  rw [← observe_rows rows repeats p slots exterior]
  change LowerCutRows.reconstruct rows repeats p slots exterior
      (CutCallExtension.original (cutSlots p slots) rows raw) =
    installRows rows repeats p slots exterior
      (LowerCutCallSplit.splitAssembled rows repeats p slots
        (CutChildGrouping.assemble (cutSlots p slots) rows
          (CutCallExtension.original (cutSlots p slots) rows raw))).1
      (LowerCutCallSplit.splitAssembled rows repeats p slots
        (CutChildGrouping.assemble (cutSlots p slots) rows
          (CutCallExtension.original (cutSlots p slots) rows raw))).2
  rw [← LowerCutAssembled.reconstruct_assemble, ← reconstruct_merge,
    LowerCutCallSplit.merge_split]

private theorem replace_replace (arrays : Arrays slots rows)
    (S T : NativeRows rows p slots) :
    SelectedArrayReplacement.replace rows p slots
        (SelectedArrayReplacement.replace rows p slots arrays S) T =
      SelectedArrayReplacement.replace rows p slots arrays T := by
  simp only [LowerCutNodeCoordinates.replace_eq_update]
  funext node
  by_cases hnode : node = WholeArrayInteriorExterior.upperNode p
  · subst node
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hnode]

theorem second_eq_installRows (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    LowerCutPair.second rows repeats p slots exterior a raw =
      installRows rows repeats p slots exterior (observe rows repeats p slots raw).1
        (SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.second rows repeats p slots exterior a raw)) := by
  rw [LowerCutPair.selected_second]
  exact (congrArg
    (fun arrays => SelectedArrayReplacement.replace rows p slots arrays
      (LowerDirectionFiber.replace a
        (SelectedArrayReplacement.selectedRows rows p slots
          (LowerCutPair.first rows repeats p slots exterior raw))
        (LowerCutPair.fresh rows repeats p slots raw)))
    (first_eq_installRows rows repeats p slots exterior raw)).trans
      (replace_replace rows p slots _ _ _)

theorem arraysPair_eq (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats p slots) :
    LowerCutPair.arraysPair rows repeats p slots exterior a raw =
      (installMatrix rows repeats p slots exterior (matrixPair rows repeats p slots exterior a raw).1
        (matrixPair rows repeats p slots exterior a raw).2.1,
       installMatrix rows repeats p slots exterior (matrixPair rows repeats p slots exterior a raw).1
        (matrixPair rows repeats p slots exterior a raw).2.2) := by
  simp only [matrixPair, LowerCutPair.matrixPair, LowerCutPair.selectedPair,
    installMatrix, EvaluationMatrix.rows_ofRows]
  exact Prod.ext (first_eq_installRows rows repeats p slots exterior raw)
    (second_eq_installRows rows repeats p slots exterior a raw)

theorem arraysPair_law_oai (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (cutSlots p slots) rows).pushforward (LowerCutPair.arraysPair rows repeats p slots exterior a) =
      ((FiniteDistribution.uniform (Complement rows repeats p slots)).product
        (((FiniteDistribution.uniform (NativeMatrix rows p slots)).product
          (FiniteDistribution.uniform (H (cutSlots p slots)))).pushforward
            (fun z => (z.1, EvaluationMatrix.shift (H (cutSlots p slots)) z.1 a.val z.2)))).pushforward
        (fun z => (installMatrix rows repeats p slots exterior z.1 z.2.1,
          installMatrix rows repeats p slots exterior z.1 z.2.2)) := by
  have h := congrArg
    (fun μ : FiniteDistribution
      (Complement rows repeats p slots × (NativeMatrix rows p slots × NativeMatrix rows p slots)) =>
      μ.pushforward (fun z => (installMatrix rows repeats p slots exterior z.1 z.2.1,
        installMatrix rows repeats p slots exterior z.1 z.2.2)))
    (matrixPair_law rows repeats p slots exterior a)
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [← arraysPair_eq] using h

end
end PerfectCompleteness.LowerCutPairBackground

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.LowerCutPairBackground.arraysPair_law_oai := @OAI.PerfectCompleteness.LowerCutPairBackground.arraysPair_law_oai
