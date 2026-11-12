-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalBucketFamily.mean_agreement_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:14:11.055665+00:00
-- url     : https://prove2.me/submissions/63b06c41-6a9a-4d4c-842a-32186811d75a

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
import Definitions.Def_OAIQ252P015
import Theorems.Thm_OAI_PerfectCompleteness_BucketQuotientAgreement_agreement_eq_nonzeroAgreement
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalBucketFamily_collision_probability_ge_eighth

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact finite total variation and its event-probability bound. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

/-- A one-sided event difference is bounded by half the total absolute mass
difference. Normalization is used; the full absolute-mass sum would lose a
factor of two needed in the repetition argument. -/
theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_le_add_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event ≤ ν.probability event + μ.totalVariation ν := by
  have h := μ.probability_sub_le_totalVariation ν event
  linarith

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_BucketQuotientAgreement
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.DecoderTableCoupling.definedEqual_collision _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BucketQuotientAgreement

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)
open PartialTableInverse (definedEquality nonzeroAgreement)

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

theorem probability_collision_eq_expectation {A B Y : Type*}
    [Fintype A] [Fintype B] [Fintype Y]
    (μ : FiniteDistribution A) (f : B → Option Y) (p q : A → B) :
    μ.probability (fun x => TwoResponseCollision.collision f (p x, q x)) =
      μ.expectation (fun x => definedEquality f (p x) (q x)) := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ∃ y, f (p x) = some y ∧ f (q x) = some y <;>
    simp [TwoResponseCollision.collision, definedEquality, h]

private theorem expectation_uniform_eq_expect {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    (FiniteDistribution.uniform A).expectation f = 𝔼 x : A, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

variable {Ω Y : Type*} [Fintype Y]
  (V : Submodule F2 (Ω → F2)) [Fintype V] [FiniteDimensional F2 V]
  (ℓ : Nat) (W : Submodule F2 V)

theorem uniform_bucket_collision_probability [Nonempty (Direction ℓ)]
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y) :
    ((FiniteDistribution.uniform (Direction ℓ)).product
      ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
        (FiniteDistribution.uniform V))).probability
      (fun p => TwoResponseCollision.collision f
        (MatrixRowQuotient.projectMatrix W
          (BucketMatrixResampling.assembledMatrix V ℓ p.2.1),
        MatrixRowQuotient.projectMatrix W
          (BucketMatrixResampling.assembledMatrix V ℓ
            (Function.update p.2.1 p.1 p.2.2)))) = nonzeroAgreement f := by
  rw [probability_collision_eq_expectation, FiniteDistribution.expectation_product,
    expectation_uniform_eq_expect]
  calc
    _ = agreement V ℓ W f := by
      unfold agreement
      apply Finset.expect_congr rfl
      intro a _
      exact (probability_collision_eq_expectation
        ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
          (FiniteDistribution.uniform V)) f
        (fun p => MatrixRowQuotient.projectMatrix W
          (BucketMatrixResampling.assembledMatrix V ℓ p.1))
        (fun p => MatrixRowQuotient.projectMatrix W
          (BucketMatrixResampling.assembledMatrix V ℓ (Function.update p.1 a p.2)))).symm
    _ = nonzeroAgreement f := agreement_eq_nonzeroAgreement V ℓ W f

end
end PerfectCompleteness.BucketQuotientAgreement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalAgreementMean
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAgreementMean

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

private theorem probability_product {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A × B → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun a => ν.probability (fun b => event (a, b))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

variable (lowerLevel : Nat) {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lower : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAgreementMean.backgroundFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAgreementMean.rowSpaceFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAgreementMean.valueFintype
theorem reference_collision_eq_mean
    (backgroundLaw : FiniteDistribution (Background (rows := rows) slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (referenceLaw slots upper backgroundLaw hrows).probability
        (collision slots upper lowerLevel original arrays lower κ σ) =
      backgroundLaw.expectation (fun background => PartialTableInverse.nonzeroAgreement
        (HierarchicalUsefulness.table slots upper lowerLevel original arrays lower κ σ background)) := by
  let : Nonempty (BucketSampler.Direction (rows (Nodes.height upper))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  rw [referenceLaw, FiniteDistribution.probability_pushforward, probability_product]
  apply FiniteDistribution.expectation_congr
  intro background
  exact BucketQuotientAgreement.uniform_bucket_collision_probability
    (NodeEmbedding.RowSpace slots upper) (rows (Nodes.height upper))
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalUsefulness.table slots upper lowerLevel original arrays lower κ σ background)

end
end PerfectCompleteness.HierarchicalAgreementMean

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CandidateCoupling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_HierarchicalBucketFamily
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalBucketFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

attribute [local instance] OAI.PerfectCompleteness.HierarchicalBucketFamily.backgroundFiberFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalBucketFamily.rowSpaceFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalBucketFamily.inputFintype
local instance valueFintype_r373619_1 (b : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Value S b) :=
  HierarchicalAdviceFamily.valueFintype S b
theorem reference_collision_eq_mean (κ : ℝ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper)) :
    (referencePairLaw S outer backgrounds hrows).probability (collision S κ) =
      (HierarchicalAdviceFamily.backgroundLaw S outer backgrounds).expectation
        (fun b => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceFamily.table S κ b)) := by
  rw [referencePairLaw, CompletionSoundness.sigmaLaw_probability,
    HierarchicalAdviceFamily.backgroundLaw, CandidateCoupling.expectation_sigmaLaw]
  apply FiniteDistribution.expectation_congr
  intro o
  exact HierarchicalAgreementMean.reference_collision_eq_mean
    (S o).slots (S o).upper (S o).lowerLevel (S o).original (S o).arrays
    (HierarchicalAdviceExperiment.lowerEvent (S o)) κ (S o).strategy (backgrounds o) (hrows o)

variable {P : O → Type*} [∀ o, Fintype (P o)]

variable (κ : ℝ) (outer : FiniteDistribution O)
  (externalLaw : (o : O) → FiniteDistribution (P o))
  (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
  (scalarLaw : (o : O) → P o →
    FiniteDistribution (NodeEmbedding.RowSpace (S o).slots (S o).upper))
  (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))

theorem mean_agreement_ge_oai
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ usefulMass S κ outer externalLaw background scalarLaw hrows)
    (hpaired : (actualPairLaw S outer externalLaw background scalarLaw hrows).totalVariation
      (referencePairLaw S outer backgrounds hrows) ≤ c ^ 2 / 16) :
    c ^ 2 / 16 ≤ (HierarchicalAdviceFamily.backgroundLaw S outer backgrounds).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (HierarchicalAdviceFamily.table S κ b)) := by
  have hcollision := collision_probability_ge_eighth S κ outer externalLaw background scalarLaw
    hrows c hc hmass
  have htransfer := FiniteDistribution.probability_le_add_totalVariation
    (actualPairLaw S outer externalLaw background scalarLaw hrows)
    (referencePairLaw S outer backgrounds hrows) (collision S κ)
  rw [reference_collision_eq_mean] at htransfer
  linarith

end
end PerfectCompleteness.HierarchicalBucketFamily

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PerfectCompleteness.HierarchicalBucketFamily.mean_agreement_ge_oai.{u_1, u_2, u_3} := @OAI.PerfectCompleteness.HierarchicalBucketFamily.mean_agreement_ge_oai.{u_1, u_2, u_3}
