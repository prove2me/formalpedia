-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedPair.exists_pair
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:28.513536+00:00
-- url     : https://prove2.me/submissions/a19bb6f6-a145-4bda-8947-356c840cf6e8

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
import Theorems.Thm_OAI_PerfectCompleteness_OriginalWholeCutComparison_totalVariation_le
import Theorems.Thm_OAI_PerfectCompleteness_PreliminaryPairReserve_exists_pair

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
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

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexDecidableEq _root_.OAI.PerfectCompleteness.RecursiveSampler.drawIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.FixedStoppedNativeProjection.flags_eq _root_.OAI.PerfectCompleteness.GeometricPrefixSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPrefixSplit.split_join _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NumberedUniformCut.numberRecordEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_below _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_exterior _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_split _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.split_assembleRecord _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedProjectedContext.directions_split _root_.OAI.PerfectCompleteness.StoppedProjectedContext.questions_split _root_.OAI.PerfectCompleteness.StoppedProjectedContext.tag_split _root_.OAI.PerfectCompleteness.UpperScalarCutBucket.numberedPairRecord_numberRecord _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

namespace PerfectCompleteness.PathComposition

open RecursiveSpaces DescendantSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n m : Nat}

theorem append_leafPath (p : Path branch n m) :
    ∀ leaf : Slots branch m, p.append (GeometricPath.leafPath leaf) =
      GeometricPath.leafPath (p.slotEmbedding leaf) := by
  induction p with
  | refl n => intro leaf; rfl
  | step i p ih =>
      intro leaf
      exact congrArg (Path.step i) (ih leaf)

end PerfectCompleteness.PathComposition

end


namespace PerfectCompleteness.GeometricCutSplit

open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

variable {branch : Nat → Nat}

theorem splitDepth_symm_eq_embedding (cutoff depth : Nat)
    (pref : PrefixDepth branch cutoff depth) (suffix : Slots branch cutoff) :
    (splitDepth cutoff depth).symm (pref, suffix) =
      (prefixPathDepth cutoff depth pref).slotEmbedding suffix := by
  revert pref
  induction depth with
  | zero => intro pref; rfl
  | succ depth ih =>
      intro pref
      change (pref.1, (splitDepth cutoff depth).symm (pref.2, suffix)) =
        (pref.1, (prefixPathDepth cutoff depth pref.2).slotEmbedding suffix)
      exact Prod.ext rfl (ih pref.2)

theorem castPath_embedding {a b cutoff : Nat} (h : a = b)
    (p : Path branch a cutoff) (suffix : Slots branch cutoff) :
    (castPath h p).slotEmbedding suffix =
      (Equiv.cast (congrArg (Slots branch) h)) (p.slotEmbedding suffix) := by
  cases h
  rfl

variable {root cutoff : Nat}

theorem joinEquiv_apply (hcut : cutoff ≤ root)
    (pref : Prefix branch root cutoff) (suffix : Slots branch cutoff) :
    joinEquiv hcut (pref, suffix) = (prefixPath hcut pref).slotEmbedding suffix := by
  rw [prefixPath, castPath_embedding]
  change (Equiv.cast (congrArg (Slots branch) (Nat.add_sub_of_le hcut)))
      ((splitDepth cutoff (root - cutoff)).symm (pref, suffix)) = _
  exact congrArg (Equiv.cast (congrArg (Slots branch) (Nat.add_sub_of_le hcut)))
    (splitDepth_symm_eq_embedding cutoff (root - cutoff) pref suffix)

@[simp] theorem split_embedding (hcut : cutoff ≤ root)
    (pref : Prefix branch root cutoff) (suffix : Slots branch cutoff) :
    splitEquiv hcut ((prefixPath hcut pref).slotEmbedding suffix) = (pref, suffix) := by
  rw [← joinEquiv_apply]
  exact (joinEquiv hcut).symm_apply_apply (pref, suffix)

theorem split_embedding_eq (hcut : cutoff ≤ root) (leaf : Slots branch root) :
    (prefixPath hcut (splitEquiv hcut leaf).1).slotEmbedding
        (splitEquiv hcut leaf).2 = leaf := by
  rw [← joinEquiv_apply]
  exact join_split hcut leaf

theorem leafPath_split (hcut : cutoff ≤ root) (leaf : Slots branch root) :
    (prefixPath hcut (splitEquiv hcut leaf).1).append
        (GeometricPath.leafPath (splitEquiv hcut leaf).2) = GeometricPath.leafPath leaf := by
  rw [PathComposition.append_leafPath, split_embedding_eq]

noncomputable section

theorem law_split (hcut : cutoff ≤ root) (hbranch : ∀ k < root, 0 < branch k) :
    (GeometricPath.law root hbranch).pushforward (splitEquiv hcut) =
      (prefixLaw hcut hbranch).product
        (GeometricPath.law cutoff
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro pair
  change (1 : ℝ) / (Fintype.card (Slots branch root) : ℝ) =
    ((1 : ℝ) / (Fintype.card (Prefix branch root cutoff) : ℝ)) *
      ((1 : ℝ) / (Fintype.card (Slots branch cutoff) : ℝ))
  rw [Fintype.card_congr (splitEquiv (branch := branch) hcut), Fintype.card_prod, Nat.cast_mul]
  simp only [one_div_mul_one_div]

theorem expectation_split (hcut : cutoff ≤ root)
    (hbranch : ∀ k < root, 0 < branch k)
    (f : Prefix branch root cutoff → Slots branch cutoff → ℝ) :
    (GeometricPath.law root hbranch).expectation
        (fun leaf => f (splitEquiv hcut leaf).1 (splitEquiv hcut leaf).2) =
      (prefixLaw hcut hbranch).expectation (fun pref =>
        (GeometricPath.law cutoff
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).expectation (f pref)) := by
  rw [← FiniteDistribution.expectation_pushforward
    (GeometricPath.law root hbranch) (splitEquiv hcut) (fun pair => f pair.1 pair.2),
    law_split, FiniteDistribution.expectation_product]

end
end PerfectCompleteness.GeometricCutSplit



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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CommonProductVariationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ConditionalVariation

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness

noncomputable section

variable {S : Type*} [Fintype S] {Ω : S → Type*} [∀ s, Fintype (Ω s)]

theorem sigma_totalVariation (μ : FiniteDistribution S)
    (P Q : (s : S) → FiniteDistribution (Ω s)) :
    (sigmaLaw μ P).totalVariation (sigmaLaw μ Q) =
      μ.expectation (fun s => (P s).totalVariation (Q s)) := by
  change (∑ z : Σ s, Ω s,
    |μ.weight z.1 * (P z.1).weight z.2 - μ.weight z.1 * (Q z.1).weight z.2|) / 2 =
      ∑ s, μ.weight s * ((∑ x : Ω s, |(P s).weight x - (Q s).weight x|) / 2)
  rw [Fintype.sum_sigma, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg (μ.nonnegative s)]
  rw [← Finset.mul_sum]
  simp only [div_eq_mul_inv, mul_assoc]

theorem observed_sigma_le {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution S) (P Q : (s : S) → FiniteDistribution (Ω s))
    (observe : (Σ s, Ω s) → Γ) :
    ((sigmaLaw μ P).pushforward observe).totalVariation
      ((sigmaLaw μ Q).pushforward observe) ≤
        μ.expectation (fun s => (P s).totalVariation (Q s)) := by
  rw [← sigma_totalVariation μ P Q]
  exact DensityVariation.variation_pushforward_le _ _ observe

theorem observed_sigma_le_of_bound {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution S) (P Q : (s : S) → FiniteDistribution (Ω s))
    (error : S → ℝ) (bound : ∀ s, (P s).totalVariation (Q s) ≤ error s)
    (observe : (Σ s, Ω s) → Γ) :
    ((sigmaLaw μ P).pushforward observe).totalVariation
      ((sigmaLaw μ Q).pushforward observe) ≤ μ.expectation error :=
  (observed_sigma_le μ P Q observe).trans (SmallBias.expectation_mono μ bound)

theorem observed_sigma_le_const {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution S) (P Q : (s : S) → FiniteDistribution (Ω s))
    (error : ℝ) (bound : ∀ s, (P s).totalVariation (Q s) ≤ error)
    (observe : (Σ s, Ω s) → Γ) :
    ((sigmaLaw μ P).pushforward observe).totalVariation
      ((sigmaLaw μ Q).pushforward observe) ≤ error := by
  simpa only [SmallBias.expectation_const] using
    observed_sigma_le_of_bound μ P Q (fun _ => error) bound observe

end
end PerfectCompleteness.ConditionalVariation


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedCallBudgetLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PrefixTests
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
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

theorem nodeAtLevel_eq (p : Path branch n cutoff) :
    ∀ (level : Fin n), cutoff ≤ level.val + 1 →
      ∀ suffix reference : Slots branch cutoff,
        GeometricPath.nodeAtLevel (p.slotEmbedding suffix) level =
          GeometricPath.nodeAtLevel (p.slotEmbedding reference) level := by
  induction p with
  | refl n =>
      intro level hlevel suffix reference
      cases n with
      | zero => exact Fin.elim0 level
      | succ n =>
          have hlast : level = Fin.last n := by
            apply Fin.ext
            simp only [Fin.val_last]
            omega
          subst level
          exact (GeometricPath.nodeAtLevel_last (branch := branch) (n := n) suffix).trans
            (GeometricPath.nodeAtLevel_last (branch := branch) (n := n) reference).symm
  | @step n cutoff i p ih =>
      intro level
      refine Fin.lastCases ?_ (fun lower => ?_) level
      · intro _ suffix reference
        exact (GeometricPath.nodeAtLevel_last (branch := branch) (n := n)
          ((Path.step i p).slotEmbedding suffix)).trans
            (GeometricPath.nodeAtLevel_last (branch := branch) (n := n)
              ((Path.step i p).slotEmbedding reference)).symm
      · intro hlevel suffix reference
        change cutoff ≤ lower.val + 1 at hlevel
        have hnode := congrArg (fun node : Nodes branch n =>
          (Sum.inr (i, node) : Nodes branch (n + 1)))
            (ih lower hlevel suffix reference)
        exact (GeometricPath.nodeAtLevel_castSucc (branch := branch) (n := n)
          ((Path.step i p).slotEmbedding suffix) lower).trans
            (hnode.trans (GeometricPath.nodeAtLevel_castSucc (branch := branch) (n := n)
              ((Path.step i p).slotEmbedding reference) lower).symm)

theorem levelNode_eq (p : Path branch n cutoff) (level : Fin n)
    (hlevel : cutoff ≤ level.val + 1) (suffix reference : Slots branch cutoff) :
    levelNode (p.slotEmbedding suffix) level = levelNode (p.slotEmbedding reference) level := by
  apply Subtype.ext
  exact nodeAtLevel_eq p level hlevel suffix reference

variable {v m t : Nat} {rows : Nat → Nat}

theorem observe_choiceAt_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (q : PreliminarySampler.Questions branch n t m)
    (arrays : Arrays (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)) rows)
    (leaf : Slots branch n) (level : Fin n) (direction : LevelDirection rows level) :
    PreliminaryStrategy.observe clauses σ (q, leaf) arrays (choiceAt rows leaf level direction) =
      observeAtLevelNode clauses σ q arrays level (levelNode leaf level) direction := rfl

theorem observe_above_cut_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (q : PreliminarySampler.Questions branch n t m)
    (arrays : Arrays (HierarchicalArrays.sourceSlots clauses (PreliminarySampler.endpoints q)) rows)
    (p : Path branch n cutoff) (level : Fin n) (hlevel : cutoff ≤ level.val + 1)
    (suffix reference : Slots branch cutoff) (direction : LevelDirection rows level) :
    PreliminaryStrategy.observe clauses σ (q, p.slotEmbedding suffix) arrays
        (choiceAt rows (p.slotEmbedding suffix) level direction) =
      PreliminaryStrategy.observe clauses σ (q, p.slotEmbedding reference) arrays
        (choiceAt rows (p.slotEmbedding reference) level direction) := by
  simp only [observe_choiceAt_eq]
  exact congrArg (fun node : LevelNode branch level =>
    observeAtLevelNode clauses σ q arrays level node direction)
      (levelNode_eq p level hlevel suffix reference)

end
end PerfectCompleteness.PrefixTests

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalDirections
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalDirections

open RecursiveSpaces HierarchicalArrays PreliminarySampler
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n : Nat}

theorem directionLaw_toCanonical (rows : Nat → Nat) (leaf : Slots branch n)
    (level : Fin n) (hrows : ∀ k, 0 < rows (k + 1)) :
    (PreliminaryAveraging.directionLaw leaf level hrows).pushforward
        (directionEquiv rows leaf level).symm = levelLaw rows hrows level := by
  let : Nonempty (PrefixTests.LevelDirection rows level) :=
    directionNonempty (rows (level.val + 1)) (hrows level.val)
  let : Nonempty (BucketSampler.Direction
      (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level)))) :=
    directionNonempty _ (by rw [GeometricPath.nodeAtLevel_height]; exact hrows level.val)
  change (FiniteDistribution.uniform
      (BucketSampler.Direction (rows (Nodes.height (GeometricPath.nodeAtLevel leaf level))))).pushforward
      (directionEquiv rows leaf level).symm =
    FiniteDistribution.uniform (PrefixTests.LevelDirection rows level)
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact UniformConditioning.uniform_transport (directionEquiv rows leaf level).symm

theorem directionsLaw_toCanonical (rows : Nat → Nat) (leaf : Slots branch n)
    (hrows : ∀ k, 0 < rows (k + 1)) :
    (CandidateCoupling.directionsLaw leaf hrows).pushforward (tupleEquiv rows leaf).symm =
      law rows n hrows := by
  change (FiniteProduct.law (fun level => PreliminaryAveraging.directionLaw leaf level hrows)).pushforward
    (fun directions level => (directionEquiv rows leaf level).symm (directions level)) = _
  rw [FiniteProduct.pushforward_map]
  apply congrArg (fun laws : (level : Fin n) →
    FiniteDistribution (PrefixTests.LevelDirection rows level) => FiniteProduct.law laws)
  funext level
  exact directionLaw_toCanonical rows leaf level hrows

variable {v m t : Nat} {rows repeats : Nat → Nat}

theorem win_eq_observe (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (level : Fin n) (e : CandidateCoupling.Shared clauses branch n t rows) :
    PreliminaryLevelPair.win clauses strategy level e =
      PreliminaryStrategy.observe clauses
        (PreliminaryStrategy.extend clauses branch n t rows repeats strategy) e.1 e.2.1
        (PrefixTests.choiceAt rows e.1.2 level
          ((tupleEquiv rows e.1.2).symm e.2.2 level)) := by
  rw [choiceAt_toCanonical]
  rfl

end
end PerfectCompleteness.CanonicalDirections

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OriginalWholeCutComparison
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem conditional_observed_totalVariation_le
    {S Γ : Type*} [Fintype S] [Fintype Γ]
    (rows repeats : Nat → Nat) (p : S → Path branch n (m + 1))
    (slots : S → Slots branch n → Fin t → MixedSupport.Slot)
    (μ : FiniteDistribution S) (hbranch : ∀ k < m + 1, 0 < branch k)
    (observe : (Σ s : S, Arrays (slots s) rows) → Γ) :
    ((CompletionSoundness.sigmaLaw μ (fun s =>
        CutContinuationAveraging.originalArrayLaw rows repeats (p s) (slots s) hbranch)).pushforward observe).totalVariation
      ((CompletionSoundness.sigmaLaw μ (fun s =>
        WholeArraySampler.law rows repeats (p s) (slots s))).pushforward observe) ≤
      Real.sqrt ((ChildBlockCardinality.bound branch m t
        (OriginalCutCalls.count rows repeats n (m + 1)) rows : ℝ) ^ 2 / branch m) / 2 := by
  exact ConditionalVariation.observed_sigma_le_const μ
    (fun s => CutContinuationAveraging.originalArrayLaw rows repeats (p s) (slots s) hbranch)
    (fun s => WholeArraySampler.law rows repeats (p s) (slots s))
    _ (fun s => totalVariation_le rows repeats (p s) (slots s) hbranch) observe

end
end PerfectCompleteness.OriginalWholeCutComparison

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedSharedEvents
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedEvents

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open StoppedSharedSampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n t cut : Nat} {branch rows repeats : Nat → Nat}

theorem actual_win_eq (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (level : Fin n) (hlevel : cut + 1 ≤ level.val + 1)
    (sample : CandidateCoupling.Shared clauses branch n t rows) :
    PreliminaryLevelPair.win clauses strategy level sample =
      win clauses strategy hcut hbranch level (forgetSuffix clauses hcut sample) := by
  rw [CanonicalDirections.win_eq_observe]
  have h := PrefixTests.observe_above_cut_eq clauses
    (PreliminaryStrategy.extend clauses branch n t rows repeats strategy)
    sample.1.1 sample.2.1
    (GeometricCutSplit.prefixPath hcut (GeometricCutSplit.splitEquiv hcut sample.1.2).1)
    level hlevel (GeometricCutSplit.splitEquiv hcut sample.1.2).2
    (referenceSuffix hcut hbranch)
    ((CanonicalDirections.tupleEquiv rows sample.1.2).symm sample.2.2 level)
  rw [GeometricCutSplit.split_embedding_eq] at h
  exact h

theorem original_pair_probability [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (i j : Fin n)
    (hi : cut + 1 ≤ i.val + 1) (hj : cut + 1 ≤ j.val + 1) :
    (originalLaw clauses rows repeats hcut hbranch hrows).probability
        (pair clauses strategy hcut hbranch i j) =
      (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).probability
        (fun sample => PreliminaryLevelPair.win clauses strategy i sample &&
          PreliminaryLevelPair.win clauses strategy j sample) := by
  rw [originalLaw, FiniteDistribution.probability_pushforward]
  apply congrArg (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).probability
  funext sample
  exact (congrArg₂ Bool.and
    (actual_win_eq clauses strategy hcut hbranch i hi sample)
    (actual_win_eq clauses strategy hcut hbranch j hj sample)).symm

end
end PerfectCompleteness.StoppedSharedEvents

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedSharedLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open PreliminarySampler StoppedSharedSampler
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

private theorem expectation_mixture {E X : Type*} [Fintype E] [Fintype X]
    (μ : FiniteDistribution E) (ν : E → FiniteDistribution X) (f : X → ℝ) :
    (μ.mixture ν).expectation f =
      μ.expectation (fun e => (ν e).expectation f) := by
  simp only [FiniteDistribution.expectation, FiniteDistribution.mixture,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

variable {v m n t cut : Nat} {branch : Nat → Nat}

private theorem conditional_expectation
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hrows : ∀ k, 0 < rows (k + 1))
    (q : Questions branch n t m) (leaf : Slots branch n)
    (f : Record clauses branch n t cut rows → ℝ) :
    (CandidateCoupling.conditionalSharedLaw clauses rows repeats hrows (q, leaf)).expectation
        (fun sample => f (forgetSuffix clauses hcut ⟨(q, leaf), sample⟩)) =
      (CanonicalDirections.law rows n hrows).expectation (fun directions =>
        (WholeArraySampler.law rows repeats (GeometricPath.leafPath leaf)
          (sourceSlots clauses (endpoints q))).expectation (fun arrays =>
            f ⟨(q, ((GeometricCutSplit.splitEquiv hcut leaf).1, directions)), arrays⟩)) := by
  rw [CandidateCoupling.conditionalSharedLaw, FiniteDistribution.expectation_product]
  calc
    _ = (WholeArraySampler.law rows repeats (GeometricPath.leafPath leaf)
        (sourceSlots clauses (endpoints q))).expectation (fun arrays =>
          (CanonicalDirections.law rows n hrows).expectation (fun directions =>
            f ⟨(q, ((GeometricCutSplit.splitEquiv hcut leaf).1, directions)), arrays⟩)) := by
      apply FiniteDistribution.expectation_congr
      intro arrays
      change (CandidateCoupling.directionsLaw leaf hrows).expectation
          (fun directions => f ⟨(q, ((GeometricCutSplit.splitEquiv hcut leaf).1,
            (CanonicalDirections.tupleEquiv rows leaf).symm directions)), arrays⟩) = _
      rw [← FiniteDistribution.expectation_pushforward
        (CandidateCoupling.directionsLaw leaf hrows)
        (CanonicalDirections.tupleEquiv rows leaf).symm
        (fun directions =>
          f ⟨(q, ((GeometricCutSplit.splitEquiv hcut leaf).1, directions)), arrays⟩),
        CanonicalDirections.directionsLaw_toCanonical]
    _ = _ := FiniteDistribution.expectation_comm _ _ _

theorem originalLaw_expectation_eq_averagedLaw [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (f : Record clauses branch n t cut rows → ℝ) :
    (originalLaw clauses rows repeats hcut hbranch hrows).expectation f =
      (averagedLaw clauses rows repeats hcut hbranch hrows).expectation f := by
  rw [originalLaw, FiniteDistribution.expectation_pushforward,
    CandidateCoupling.sharedLaw, CandidateCoupling.expectation_sigmaLaw,
    averagedLaw, CandidateCoupling.expectation_sigmaLaw]
  simp only [baseLaw, contextLaw, FiniteDistribution.expectation_product,
    CutContinuationAveraging.originalArrayLaw, expectation_mixture]
  apply FiniteDistribution.expectation_congr
  intro q
  let value (pref : GeometricCutSplit.Prefix branch n (cut + 1))
      (suffix : Slots branch (cut + 1)) (directions : CanonicalDirections.Tuple rows n) : ℝ :=
    (WholeArraySampler.law rows repeats
      ((GeometricCutSplit.prefixPath hcut pref).append (GeometricPath.leafPath suffix))
      (sourceSlots clauses (endpoints q))).expectation (fun arrays =>
        f ⟨(q, (pref, directions)), arrays⟩)
  calc
    _ = (GeometricPath.law n hbranch).expectation (fun leaf =>
        (CanonicalDirections.law rows n hrows).expectation (fun directions =>
          value (GeometricCutSplit.splitEquiv hcut leaf).1
            (GeometricCutSplit.splitEquiv hcut leaf).2 directions)) := by
      apply FiniteDistribution.expectation_congr
      intro leaf
      rw [conditional_expectation clauses rows repeats hcut hrows q leaf f]
      apply FiniteDistribution.expectation_congr
      intro directions
      dsimp only [value]
      rw [GeometricCutSplit.leafPath_split]
    _ = (GeometricCutSplit.prefixLaw hcut hbranch).expectation (fun pref =>
        (GeometricPath.law (cut + 1)
          (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut))).expectation (fun suffix =>
            (CanonicalDirections.law rows n hrows).expectation (value pref suffix))) :=
      GeometricCutSplit.expectation_split hcut hbranch
        (fun pref suffix => (CanonicalDirections.law rows n hrows).expectation
          (value pref suffix))
    _ = _ := by
      apply FiniteDistribution.expectation_congr
      intro pref
      exact FiniteDistribution.expectation_comm _ _ (value pref)

theorem originalLaw_eq_averagedLaw [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    originalLaw (t := t) clauses rows repeats hcut hbranch hrows =
      averagedLaw clauses rows repeats hcut hbranch hrows := by
  apply SigmaObservation.eq_of_probability_eq
  intro event
  rw [CandidateCoupling.probability_eq_expectation,
    CandidateCoupling.probability_eq_expectation]
  exact originalLaw_expectation_eq_averagedLaw clauses rows repeats hcut hbranch hrows
    (fun record => if event record then 1 else 0)

end
end PerfectCompleteness.StoppedSharedLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedSharedComparison
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedSharedComparison

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open StoppedSharedSampler
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {v m n t cut : Nat} {branch rows repeats : Nat → Nat}

theorem observed_totalVariation_le [NeZero m] {Γ : Type*} [Fintype Γ]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
    (observe : Record clauses branch n t cut rows → Γ) :
    ((originalLaw clauses rows repeats hcut hbranch hrows).pushforward observe).totalVariation
      ((stoppedLaw clauses rows repeats hcut hbranch hrows).pushforward observe) ≤
      error branch rows repeats n cut t := by
  rw [StoppedSharedLaw.originalLaw_eq_averagedLaw]
  exact OriginalWholeCutComparison.conditional_observed_totalVariation_le rows repeats
    (fun context : Context branch n t m cut rows =>
      GeometricCutSplit.prefixPath hcut context.2.1)
    (fun context => sourceSlots clauses (PreliminarySampler.endpoints context.1))
    (contextLaw hcut hbranch hrows)
    (fun k hk => hbranch k (Nat.lt_of_lt_of_le hk hcut)) observe

theorem totalVariation_le [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hcut : cut + 1 ≤ n)
    (hbranch : ∀ k < n, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1)) :
    (originalLaw (t := t) clauses rows repeats hcut hbranch hrows).totalVariation
      (stoppedLaw (t := t) clauses rows repeats hcut hbranch hrows) ≤
      error branch rows repeats n cut t := by
  simpa only [FiniteDistribution.pushforward_id] using
    observed_totalVariation_le clauses rows repeats hcut hbranch hrows
      (id : Record clauses branch n t cut rows → Record clauses branch n t cut rows)

theorem pair_probability_transfer [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (i j : Fin n)
    (hi : cut + 1 ≤ i.val + 1) (hj : cut + 1 ≤ j.val + 1) :
    (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).probability
        (fun sample => PreliminaryLevelPair.win clauses strategy i sample &&
          PreliminaryLevelPair.win clauses strategy j sample) ≤
      (stoppedLaw clauses rows repeats hcut hbranch hrows).probability
        (StoppedSharedEvents.pair clauses strategy hcut hbranch i j) +
          error branch rows repeats n cut t := by
  have h := FiniteDistribution.probability_le_add_totalVariation
    (originalLaw clauses rows repeats hcut hbranch hrows)
    (stoppedLaw clauses rows repeats hcut hbranch hrows)
    (StoppedSharedEvents.pair clauses strategy hcut hbranch i j)
  rw [StoppedSharedEvents.original_pair_probability clauses strategy hcut hbranch hrows i j hi hj] at h
  exact h.trans (add_le_add le_rfl
    (totalVariation_le (t := t) clauses rows repeats hcut hbranch hrows))

theorem pair_probability_lower [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (strategy : PreliminaryStrategy.Strategy clauses branch n t rows repeats)
    (hcut : cut + 1 ≤ n) (hbranch : ∀ k < n, 0 < branch k)
    (hrows : ∀ k, 0 < rows (k + 1)) (i j : Fin n)
    (hi : cut + 1 ≤ i.val + 1) (hj : cut + 1 ≤ j.val + 1)
    {mass : ℝ} (hmass : mass ≤
      (CandidateCoupling.sharedLaw clauses rows repeats hbranch hrows).probability
        (fun sample => PreliminaryLevelPair.win clauses strategy i sample &&
          PreliminaryLevelPair.win clauses strategy j sample)) :
    mass - error branch rows repeats n cut t ≤
      (stoppedLaw clauses rows repeats hcut hbranch hrows).probability
        (StoppedSharedEvents.pair clauses strategy hcut hbranch i j) := by
  have h := pair_probability_transfer clauses strategy hcut hbranch hrows i j hi hj
  linarith

end
end PerfectCompleteness.StoppedSharedComparison

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedError
attribute [-instance] _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedError

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem original_calls_le {root cutoff : Nat}
    (hroot : root ≤ p.plan.depth) (hcut : cutoff ≤ root) :
    OriginalCutCalls.count (rows p.plan) (repeats p.plan) root cutoff ≤ calls p.plan := by
  have h := FixedCallBudget.pairCount_le (rows p.plan) (repeats p.plan)
    hroot (hcut.trans hroot)
  unfold FixedCallBudget.pairCount at h
  unfold calls
  omega

theorem hidden_error_lt {retained : Nat} (hcalls : retained ≤ calls p.plan) (height : Nat) :
    Real.sqrt ((ChildBlockCardinality.bound (branch p) height (sourceLength p.plan hδ)
      retained (rows p.plan) : ℝ) ^ 2 / branch p height) / 2 < p.accuracy := by
  have h := (FixedComparisonErrors.comparison_errors p hcalls height).1
  simpa only [branch, Nat.cast_pow] using h

theorem stopped_error_lt {root cut : Nat}
    (hroot : root ≤ p.plan.depth) (hcut : cut + 1 ≤ root) :
    StoppedSharedComparison.error (branch p) (rows p.plan) (repeats p.plan)
      root cut (sourceLength p.plan hδ) < p.accuracy :=
  hidden_error_lt p (original_calls_le p hroot hcut) cut

end
end PerfectCompleteness.FixedStoppedError

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedPair
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedPair

open FixedParameters FixedRows

noncomputable section

variable {δ : ℚ} {hδ : 0 < δ} (p : Parameters δ hδ)

theorem exists_pair_oai (input : List Bool) (strategy : FixedPreliminaryGame.Strategy p input)
    (hsuccess : InitialParameters.epsilon δ ≤
      (FixedPreliminaryGame.game p input).success strategy) :
    ∃ i j : Fin p.plan.depth, i < j ∧
      InitialParameters.simultaneous δ + 2 * p.accuracy ≤
        (StoppedSharedSampler.stoppedLaw
          (PCPSource.clauseFamily (BinaryLanguage.totalRename input))
          (rows p.plan) (repeats p.plan) (cut := i.val)
          (Nat.succ_le_of_lt i.isLt) (fun k _ => branch_pos p k)
          (fun k => FixedPreliminaryGame.rows_pos p (k + 1))).probability
            (StoppedSharedEvents.pair
              (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy
              (Nat.succ_le_of_lt i.isLt) (fun k _ => branch_pos p k) i j) := by
  obtain ⟨i, j, hij, hmass⟩ := PreliminaryPairReserve.exists_pair p input strategy hsuccess
  have hcut : i.val + 1 ≤ p.plan.depth := Nat.succ_le_of_lt i.isLt
  have hi : i.val + 1 ≤ i.val + 1 := le_refl _
  have hj : i.val + 1 ≤ j.val + 1 := Nat.add_le_add_right (Nat.le_of_lt hij) 1
  have htransfer := StoppedSharedComparison.pair_probability_lower
    (PCPSource.clauseFamily (BinaryLanguage.totalRename input)) strategy
    hcut (fun k _ => branch_pos p k)
    (fun k => FixedPreliminaryGame.rows_pos p (k + 1)) i j hi hj hmass
  have herror := FixedStoppedError.stopped_error_lt p (le_refl p.plan.depth) hcut
  refine ⟨i, j, hij, ?_⟩
  linarith

end
end PerfectCompleteness.FixedStoppedPair

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedPair.exists_pair_oai := @OAI.PerfectCompleteness.FixedStoppedPair.exists_pair_oai
