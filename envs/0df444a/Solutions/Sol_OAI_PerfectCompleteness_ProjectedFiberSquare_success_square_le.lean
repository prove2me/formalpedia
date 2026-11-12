-- Prove2me | solution 1 for OAI.PerfectCompleteness.ProjectedFiberSquare.success_square_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:20:15.806521+00:00
-- url     : https://prove2.me/submissions/62744ab7-b0ce-420d-9989-a98ca326f5a8

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
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

theorem expectation_table_eval [DecidableEq Q] (responses : Q → FiniteDistribution A)
    (q₀ : Q) (h : A → ℝ) :
    (table responses).expectation (fun answers => h (answers q₀)) =
      (responses q₀).expectation h := by
  classical
  change (∑ answers : Q → A,
    (∏ q, (responses q).weight (answers q)) * h (answers q₀)) =
      ∑ a, (responses q₀).weight a * h a
  calc
    _ = ∑ answers : Q → A,
        ∏ q, (responses q).weight (answers q) *
          (if q = q₀ then h (answers q) else 1) := by
      apply Finset.sum_congr rfl
      intro answers _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ q, ∑ a, (responses q).weight a * (if q = q₀ then h a else 1) :=
      (Fintype.prod_sum (fun q a =>
        (responses q).weight a * (if q = q₀ then h a else 1))).symm
    _ = ∏ q : Q, if q = q₀ then (∑ a, (responses q₀).weight a * h a) else 1 := by
      apply Finset.prod_congr rfl
      intro q _
      by_cases hq : q = q₀
      · subst q
        simp
      · simp [hq, (responses q).normalized]
    _ = _ := by simp

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
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Finite weighted Cauchy–Schwarz for probability weights. The summands
need not be nonnegative. -/
theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_LinearEvaluationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DirectionQuotient

variable {V B : Type*} [AddCommGroup V] [Module F2 V]

theorem mem_line_iff (a x : V) : x ∈ line a ↔ x = 0 ∨ x = a := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    rcases UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases c with hzero | hone
    · left
      simpa only [hzero, zero_smul] using hc.symm
    · right
      simpa only [hone, one_smul] using hc.symm
  · rintro (rfl | rfl)
    · exact (line a).zero_mem
    · exact Submodule.mem_span_singleton_self _

theorem proj_eq_zero_iff (a x : V) : proj a x = 0 ↔ x = 0 ∨ x = a :=
  (Submodule.Quotient.mk_eq_zero (line a)).trans (mem_line_iff a x)

open MixedSupport CanonicalKeys

end PerfectCompleteness.DirectionQuotient

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CollisionAveragingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CollisionAveraging

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

variable {B : Type*} [Fintype B]

theorem mean_square_le (μ : FiniteDistribution B) (p : B → ℝ) :
    μ.expectation p ^ 2 ≤ μ.expectation (fun b => p b ^ 2) :=
  UniqueGamesTheorem.Foundations.Information.weighted_sum_sq_le μ.weight p
    ⟨μ.nonnegative, μ.normalized⟩

end
end PerfectCompleteness.CollisionAveraging


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderTableCoupling
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DecoderTableCoupling

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {Q A : Type*} [Fintype Q] [DecidableEq Q] [Fintype A]

theorem probability_eq_expectation {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (event : X → Bool) :
    μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite,
    mul_one, mul_zero]

end
end PerfectCompleteness.DecoderTableCoupling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_MultiplicationFormInjectiveLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.SingleResponseResampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {B : Type*} [Fintype B]
  {Ω Y : B → Type*} [∀ b, Fintype (Ω b)] [∀ b, Fintype (Y b)]

theorem probability_rectangle {A C : Type*} [Fintype A] [Fintype C]
    (μ : FiniteDistribution A) (ν : FiniteDistribution C)
    (p : A → Bool) (q : C → Bool) :
    (μ.product ν).probability (fun x => p x.1 && q x.2) =
      μ.probability p * ν.probability q := by
  unfold FiniteDistribution.probability
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro c _
  cases hp : p a <;> cases hq : q c <;> simp [FiniteDistribution.product, hp, hq]

end
end PerfectCompleteness.SingleResponseResampling


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ChildBlockProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ChildBlockProjection

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

theorem restrictNode_projection
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (node : Nodes branch n) (x : Domain slots) :
    sourceProjection (nodeProjection p node) (restrictNode slots node x) =
      restrictNode projected node (sourceProjection p x) := rfl

end
end PerfectCompleteness.ChildBlockProjection

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RightDecoderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RightDecoderDescendant

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open PointwiseSpaces TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper lower : Nodes branch n) (cut : Cut upper lower)

theorem restriction_restrictNode (x : Domain slots) :
    restriction slots upper lower cut (restrictNode slots upper x) =
      restrictNode slots lower x := by
  have cast_apply :
      ∀ (i j : RecursiveSpaces.Slots branch n) (_ : i = j)
        (hA : LeafDomain slots i = LeafDomain slots j),
        Equiv.cast hA (x i) = x j := by
    intro i j hij hA
    subst j
    rfl
  funext s
  exact cast_apply _ _ (cut.slots_agree s)
    (congrFun (Cut.family_eq (slots := slots) (upper := upper) (lower := lower) cut) s)

variable (hbranch : ∀ k < Nodes.height upper, 0 < branch k)

theorem squareEmbedding_restrictNode
    (f : squareSpace (H (nodeSlots slots lower))) (x : Domain slots) :
    (squareEmbedding slots upper lower cut hbranch f).val (restrictNode slots upper x) =
      f.val (restrictNode slots lower x) := by
  rw [squareEmbedding_apply, restriction_restrictNode]


end
end PerfectCompleteness.RightDecoderDescendant

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderSourcePullback
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DecoderSourcePullback

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces OwnInputReference
open ChildBlockProjection

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

variable (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
  (upper lower : Nodes branch n) (cut : Cut upper lower)

theorem restriction_projection (x : Domain (nodeSlots slots upper)) :
    RightDecoderDescendant.restriction projected upper lower cut
        (sourceProjection (nodeProjection p upper) x) =
      sourceProjection (nodeProjection p lower)
        (RightDecoderDescendant.restriction slots upper lower cut x) := by
  obtain ⟨y, rfl⟩ := restrictNode_surjective slots upper x
  rw [restrictNode_projection, RightDecoderDescendant.restriction_restrictNode,
    RightDecoderDescendant.restriction_restrictNode]
  exact (restrictNode_projection p lower y).symm

theorem squareEmbedding_pullback
    (hbranch : ∀ k < Nodes.height upper, 0 < branch k) :
    (HPullback (nodeProjection p upper)).comp
        (RightDecoderDescendant.squareEmbedding projected upper lower cut hbranch) =
      (RightDecoderDescendant.squareEmbedding slots upper lower cut hbranch).comp
        (squarePullback (nodeProjection p lower)) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change f.val (RightDecoderDescendant.restriction projected upper lower cut
      (sourceProjection (nodeProjection p upper) x)) =
    f.val (sourceProjection (nodeProjection p lower)
      (RightDecoderDescendant.restriction slots upper lower cut x))
  rw [restriction_projection p upper lower cut]

theorem squarePullback_product (f g : H projected) :
    squarePullback p (OddListExtraction.productElement (H projected) f g) =
      OddListExtraction.productElement (H slots) (HPullback p f) (HPullback p g) := by
  apply Subtype.ext
  rfl


variable (level : Nat) (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

theorem embed_squareEmbedding
    (cut : Cut upper (HierarchicalLeftDecoder.LowerNode upper level d)) :
    (NodeEmbedding.embed slots upper).comp
        (RightDecoderDescendant.squareEmbedding slots upper
          (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)) =
      HierarchicalLeftDecoder.squareEmbedding slots upper level hbranch d := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (RightDecoderDescendant.squareEmbedding slots upper
      (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch) f).val
        (restrictNode slots upper ((TreeCanonical.assignmentEquiv slots).symm x)) =
    f.val (restrictNode slots (HierarchicalLeftDecoder.LowerNode upper level d)
      ((TreeCanonical.assignmentEquiv slots).symm x))
  exact RightDecoderDescendant.squareEmbedding_restrictNode slots upper
    (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch) f
    ((TreeCanonical.assignmentEquiv slots).symm x)

theorem functional_upperTarget
    (cut : Cut upper (HierarchicalLeftDecoder.LowerNode upper level d))
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    RightDecoderDescendant.functional projected upper
        (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
        (upperTarget p upper q) =
      (HierarchicalLeftDecoder.output slots upper level hbranch d q).comp
        (squarePullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d))) := by
  apply LinearMap.ext
  intro f
  change q (NodeEmbedding.embed slots upper
      (HPullback (nodeProjection p upper)
        (RightDecoderDescendant.squareEmbedding projected upper
          (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch) f))) =
    q (HierarchicalLeftDecoder.squareEmbedding slots upper level hbranch d
      (squarePullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) f))
  calc
    _ = q (NodeEmbedding.embed slots upper
        (RightDecoderDescendant.squareEmbedding slots upper
          (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
          (squarePullback (nodeProjection p
            (HierarchicalLeftDecoder.LowerNode upper level d)) f))) :=
      congrArg (fun g => q (NodeEmbedding.embed slots upper g))
        (LinearMap.congr_fun (squareEmbedding_pullback p upper
          (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)) f)
    _ = _ := congrArg q (LinearMap.congr_fun
      (embed_squareEmbedding (slots := slots) upper level hbranch d cut)
      (squarePullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) f))

theorem form_upperTarget
    (cut : Cut upper (HierarchicalLeftDecoder.LowerNode upper level d))
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (f g : H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) :
    RightDecoderDescendant.form projected upper
        (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
        (upperTarget p upper q) f g =
      OddListExtraction.multiplicationForm
        (H (nodeSlots slots (HierarchicalLeftDecoder.LowerNode upper level d)))
        (HierarchicalLeftDecoder.output slots upper level hbranch d q)
        (HPullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) f)
        (HPullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d)) g) := by
  change RightDecoderDescendant.functional projected upper
      (HierarchicalLeftDecoder.LowerNode upper level d) cut (upperBranch upper hbranch)
      (upperTarget p upper q)
      (OddListExtraction.productElement
        (H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) f g) = _
  rw [functional_upperTarget p upper level hbranch d cut q]
  change (HierarchicalLeftDecoder.output slots upper level hbranch d q)
      (squarePullback (nodeProjection p (HierarchicalLeftDecoder.LowerNode upper level d))
        (OddListExtraction.productElement
          (H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) f g)) = _
  rw [squarePullback_product]
  rfl


end
end PerfectCompleteness.DecoderSourcePullback

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerDirectionFiber
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
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

theorem quotient_replace (a : Direction ℓ) (S : Rows H ℓ) (fresh : H)
    (eval : H →ₗ[F2] F2) :
    DirectionQuotient.proj a.val (fun i => eval (replace a S fresh i)) =
      DirectionQuotient.proj a.val (fun i => eval (S i)) := by
  have heq : (fun i => eval (replace a S fresh i)) =
      (fun i => eval (S i)) + eval (fresh - S (pivot a)) • a.val := by
    rw [replace_eq]
    funext i
    simp only [Pi.add_apply, BucketSampler.rankOne, map_add, map_smul,
      Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [heq, map_add, map_smul]
  have hz : DirectionQuotient.proj a.val a.val = 0 :=
    (DirectionQuotient.proj_eq_zero_iff a.val a.val).mpr (Or.inr rfl)
  rw [hz, smul_zero, add_zero]

section ActualFunctions

variable {X : Type*} (V : Submodule F2 (X → F2))

@[simp] theorem quotientQuery_replace (a : Direction ℓ) (S : Rows V ℓ) (fresh : V) :
    quotientQuery V a (replace a S fresh) = quotientQuery V a S := by
  funext x
  exact quotient_replace a S fresh (EvaluationMatrix.evaluation V x)

end ActualFunctions

end
end PerfectCompleteness.LowerDirectionFiber

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_LowerCutOwnInput
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutOwnInput

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior
open scoped Classical TensorProduct

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : Slots branch n → Fin t → MixedSupport.Slot) (rows : Nat → Nat)
  (upper lower : Nodes branch n)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))

theorem ofArrays_update
    (a : BucketSampler.Direction (rows (Nodes.height lower)))
    (known : HiddenBucketBias.VisibleDirection W → OwnInputReference.UpperSpace slots upper)
    (arrays : Arrays slots rows) (fresh : H (nodeSlots slots lower)) :
    ofArrays slots rows upper lower W a.val known
        (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh)) =
      ofArrays slots rows upper lower W a.val known arrays := by
  have hother :
      (fun node : OwnInputReference.OtherNodes upper lower =>
        Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh) node.val) =
      (fun node : OwnInputReference.OtherNodes upper lower => arrays node.val) := by
    funext node
    exact Function.update_of_ne node.property.2 _ _
  change
    (OwnInputReference.Input.mk known
      (fun node : OwnInputReference.OtherNodes upper lower =>
        Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh) node.val)
      (LowerDirectionFiber.quotientQuery (H (nodeSlots slots lower)) a
        (Function.update arrays lower (LowerDirectionFiber.replace a (arrays lower) fresh) lower))) =
    (OwnInputReference.Input.mk known
      (fun node : OwnInputReference.OtherNodes upper lower => arrays node.val)
      (LowerDirectionFiber.quotientQuery (H (nodeSlots slots lower)) a (arrays lower)))
  rw [hother, Function.update_self, LowerDirectionFiber.quotientQuery_replace]

end
end PerfectCompleteness.LowerCutOwnInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ProjectedLowerFiber
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedLowerFiber

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

theorem rightInput_fixed {r : Nat}
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d)
    (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d) :
    LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
        (LinearMap.ker A) a.val known (arraysAt projected upper level d a arrays fresh) =
      LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
        (LinearMap.ker A) a.val known arrays :=
  LowerCutOwnInput.ofArrays_update projected rows upper (lower upper level d)
    (LinearMap.ker A) a known arrays fresh

theorem rightLaw_fixed {r : Nat}
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (a : Direction (rows := rows) upper level d)
    (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
      OwnInputReference.UpperSpace projected upper)
    (arrays : Arrays projected rows) (fresh : Scalar projected upper level d)
    (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper (lower upper level d))
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t)) (threshold : ℝ) :
    RightDecoder.law projected rows upper (lower upper level d) (LinearMap.ker A) a.val
        repeats cut σ
        (LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
          (LinearMap.ker A) a.val known (arraysAt projected upper level d a arrays fresh)) threshold =
      RightDecoder.law projected rows upper (lower upper level d) (LinearMap.ker A) a.val
        repeats cut σ
        (LowerCutOwnInput.ofArrays projected rows upper (lower upper level d)
          (LinearMap.ker A) a.val known arrays) threshold := by
  rw [rightInput_fixed projected upper level d A a known arrays fresh]

end
end PerfectCompleteness.ProjectedLowerFiber

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ProjectedNativeCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedNativeCollision

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
  (p : ∀ leaf k, MixedSupport.Projection (slots leaf k) (projected leaf k))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

theorem form_eq_on_pullbacks
    (q0 q1 : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (htarget : DecoderSourcePullback.upperTarget p upper q0 =
      DecoderSourcePullback.upperTarget p upper q1)
    (f g : H (nodeSlots projected (HierarchicalLeftDecoder.LowerNode upper level d))) :
    OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH slots upper level d)
        (HierarchicalLeftDecoder.output slots upper level hbranch d q0)
        (HPullback (ChildBlockProjection.nodeProjection p
          (HierarchicalLeftDecoder.LowerNode upper level d)) f)
        (HPullback (ChildBlockProjection.nodeProjection p
          (HierarchicalLeftDecoder.LowerNode upper level d)) g) =
      OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH slots upper level d)
        (HierarchicalLeftDecoder.output slots upper level hbranch d q1)
        (HPullback (ChildBlockProjection.nodeProjection p
          (HierarchicalLeftDecoder.LowerNode upper level d)) f)
        (HPullback (ChildBlockProjection.nodeProjection p
          (HierarchicalLeftDecoder.LowerNode upper level d)) g) := by
  have h0 := DecoderSourcePullback.form_upperTarget p upper level hbranch d
    (DecoderSourcePullback.selectedCut upper level d) q0 f g
  have h1 := DecoderSourcePullback.form_upperTarget p upper level hbranch d
    (DecoderSourcePullback.selectedCut upper level d) q1 f g
  rw [htarget] at h0
  exact h0.symm.trans h1

theorem decode_eq_some_of_high (s : Nat)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (hhigh : s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q)) :
    HierarchicalDecoderTables.decode slots upper level hbranch d s q =
      some (HierarchicalLeftDecoder.output slots upper level hbranch d q) := by
  exact ite_eq_right (Nat.not_le.mpr hhigh)

theorem two_high_hits_restricted (s : Nat)
    (q0 q1 : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (right : Module.Dual F2 (OwnInputReference.UpperSpace projected upper))
    (hrank0 : s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q0))
    (hrank1 : s < HierarchicalDecoderTables.fullRank slots upper level d
      (HierarchicalLeftDecoder.output slots upper level hbranch d q1))
    (hhit0 : DecoderSourcePullback.upperTarget p upper q0 = right)
    (hhit1 : DecoderSourcePullback.upperTarget p upper q1 = right) :
    BilinearCollisionTransfer.restrictedCollision
      ((HierarchicalDecoderTables.decode slots upper level hbranch d s q0).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)))
      ((HierarchicalDecoderTables.decode slots upper level hbranch d s q1).map
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper level d)))
      (LinearMap.range (HPullback (ChildBlockProjection.nodeProjection p
        (HierarchicalLeftDecoder.LowerNode upper level d)))) = true := by
  rw [decode_eq_some_of_high upper level hbranch d s q0 hrank0,
    decode_eq_some_of_high upper level hbranch d s q1 hrank1]
  apply decide_eq_true
  refine ⟨_, _, rfl, rfl, ?_⟩
  rintro v ⟨f, rfl⟩ w ⟨g, rfl⟩
  exact form_eq_on_pullbacks p upper level hbranch d q0 q1
    (hhit0.trans hhit1.symm) f g

end
end PerfectCompleteness.ProjectedNativeCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedFiberSquare
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberSquare

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open ProjectedLowerFiber

attribute [local instance] RightDecoder.scalarFintype

private theorem table_sampling {Q Y Z Ω : Type*}
    [Fintype Q] [DecidableEq Q] [Fintype Y] [Fintype Z] [Fintype Ω]
    (responses : Q → FiniteDistribution Y) (right : FiniteDistribution Z)
    (ν : FiniteDistribution Ω) (question : Ω → Q) (event : Ω → Y × Z → Bool) :
    ν.expectation (fun x => ((responses (question x)).product right).probability (event x)) =
      ((FiniteDistribution.table responses).product right).expectation
        (fun seed => ν.probability (fun x => event x (seed.1 (question x), seed.2))) := by
  simp_rw [DecoderTableCoupling.probability_eq_expectation]
  symm
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro x
  simp only [FiniteDistribution.expectation_product]
  exact FiniteDistribution.expectation_table_eval responses (question x)
    (fun y => right.expectation (fun z => if event x (y, z) then (1 : ℝ) else 0))

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
  (a : Direction (rows := rows) upper level d) (arrays : Arrays projected rows)

local instance rowSpaceFintype_r901937_1 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_r901937_1 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
theorem fixed_seed_square (s : Nat)
    (ν : FiniteDistribution (Scalar projected upper level d))
    (table : UpperTable (rows := rows) slots upper level r)
    (right : Module.Dual F2 (OwnInputReference.UpperSpace projected upper)) :
    ν.probability (fun fresh => highMeeting slots projected projection upper level hbranch d s
        (upperAt slots projected projection upper level d A a arrays table fresh) right) ^ 2 ≤
      (ν.product ν).probability
        (restrictedPair slots projected projection upper level hbranch d A a arrays s table) := by
  rw [pow_two, ← SingleResponseResampling.probability_rectangle]
  apply FiniteDistribution.probability_mono
  intro pair hpair
  obtain ⟨h0, h1⟩ := Bool.and_eq_true_iff.mp hpair
  obtain ⟨hrank0, hhit0⟩ := of_decide_eq_true h0
  obtain ⟨hrank1, hhit1⟩ := of_decide_eq_true h1
  exact ProjectedNativeCollision.two_high_hits_restricted projection upper level hbranch d s
    (upperAt slots projected projection upper level d A a arrays table pair.1)
    (upperAt slots projected projection upper level d A a arrays table pair.2)
    right hrank0 hrank1 hhit0 hhit1

variable
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
    OwnInputReference.UpperSpace projected upper)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper (lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

theorem success_eq_seed_mean (s : Nat)
    (ν : FiniteDistribution (Scalar projected upper level d)) :
    success slots projected projection upper level hbranch d A a arrays known
        repeats cut σ useful ρ threshold s ν =
      (seedLaw slots projected upper level d A a arrays known repeats cut σ useful ρ threshold).expectation
        (fun seed => ν.probability (fun fresh =>
          highMeeting slots projected projection upper level hbranch d s
            (upperAt slots projected projection upper level d A a arrays seed.1 fresh) seed.2)) := by
  unfold success
  simp_rw [ProjectedLowerFiber.rightLaw_fixed projected upper level d A a known arrays]
  exact table_sampling
    (HierarchicalAllDecoderTables.upperKernel slots upper level σ useful r ρ)
    (rightLaw projected upper level d A a arrays known repeats cut σ threshold) ν
    (inputAt slots projected projection upper level d A a arrays)
    (fun _ pair => highMeeting slots projected projection upper level hbranch d s pair.1 pair.2)

theorem success_square_le_oai (s : Nat)
    (ν : FiniteDistribution (Scalar projected upper level d)) :
    success slots projected projection upper level hbranch d A a arrays known
        repeats cut σ useful ρ threshold s ν ^ 2 ≤
      (seedLaw slots projected upper level d A a arrays known repeats cut σ useful ρ threshold).expectation
        (fun seed => (ν.product ν).probability
          (restrictedPair slots projected projection upper level hbranch d A a arrays s seed.1)) := by
  rw [success_eq_seed_mean]
  apply (CollisionAveraging.mean_square_le _ _).trans
  apply Finset.sum_le_sum
  intro seed _
  exact mul_le_mul_of_nonneg_left
    (fixed_seed_square slots projected projection upper level hbranch d A a arrays
      s ν seed.1 seed.2)
    ((seedLaw slots projected upper level d A a arrays known repeats cut σ useful ρ threshold).nonnegative seed)

end
end PerfectCompleteness.ProjectedFiberSquare

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.ProjectedFiberSquare.success_square_le_oai := @OAI.PerfectCompleteness.ProjectedFiberSquare.success_square_le_oai
