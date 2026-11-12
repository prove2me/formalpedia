-- Prove2me | solution 1 for OAI.PerfectCompleteness.CleanDecoderRate.bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:14:05.895372+00:00
-- url     : https://prove2.me/submissions/825b6188-9c5d-4305-a1d9-66d7472e1c47

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
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalLeftDecoder_adviceLaw_valid
import Theorems.Thm_OAI_PerfectCompleteness_UniformCleanSoundness_source_soundness

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddLists
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OddLists

open scoped BigOperators

variable {A B : Type*} {s : Nat}

section Parity

variable [Fintype B] [DecidableEq B]

theorem mem_parityPushforward_iff_sum (π : A → B) (L : Finset A) (b : B) :
    b ∈ parityPushforward π L ↔
      (∑ a ∈ L, if π a = b then (1 : ZMod 2) else 0) = 1 := by
  rw [mem_parityPushforward, Finset.sum_boole]
  exact ZMod.natCast_eq_one_iff_odd.symm

end Parity

section Supports

variable [Fintype A]

theorem parityPushforward_support [Fintype B] [DecidableEq B]
    (π : A → B) (f : A → ZMod 2) :
    parityPushforward π (support f) =
      support (fun b => ∑ a, if π a = b then f a else 0) := by
  ext b
  rw [mem_parityPushforward_iff_sum, mem_support]
  have hsum : (∑ a ∈ support f, if π a = b then (1 : ZMod 2) else 0) =
      ∑ a, if π a = b then f a else 0 := by
    unfold support
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    rcases binary_cases (f a) with hzero | hone
    · simp [hzero]
    · simp [hone]
  rw [hsum]

end Supports

end PerfectCompleteness.OddLists

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_RepetitionRateLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RepetitionRate

open scoped BigOperators
open UniqueGamesTheorem.Foundations Games

theorem halfRate_cast (L : Nat) :
    (halfRate L : ℝ) = 1 - 1 / (48000 * (L : ℝ)) := by
  simp only [halfRate, Rat.cast_sub, Rat.cast_one, Rat.cast_div,
    Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]

end PerfectCompleteness.RepetitionRate



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourceOddListsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.SourceAnswerEquiv

open SourceClause

variable {v m t : Nat}

theorem projection_decode (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t) (a : SourceOddLists.LeftLabels t) :
    actualProjection clauses e ((leftEquiv clauses (SourceOddLists.left e)).symm a) =
      (rightEquiv clauses (SourceOddLists.right clauses e)).symm
        (SourceOddLists.projection clauses e a) := rfl

theorem projection_encode (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t)
    (a : LeftDomain clauses (SourceOddLists.left e)) :
    rightEquiv clauses (SourceOddLists.right clauses e) (actualProjection clauses e a) =
      SourceOddLists.projection clauses e (leftEquiv clauses (SourceOddLists.left e) a) := by
  have h := projection_decode clauses e (leftEquiv clauses (SourceOddLists.left e) a)
  rw [Equiv.symm_apply_apply] at h
  exact congrArg (rightEquiv clauses (SourceOddLists.right clauses e)) h


end PerfectCompleteness.SourceAnswerEquiv

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_NativeLeafAlphabet
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.NativeLeafAlphabet

open SourceClause

variable {I : Type*} {v m t : Nat}

theorem projection_encode (clauses : Fin m → NormalizedClause v)
    (e : SourceOddLists.Occurrences m t) {a b : Fin t → MixedSupport.Slot}
    (ha : a = SourceAnswerEquiv.leftSlots clauses (SourceOddLists.left e))
    (hb : b = SourceAnswerEquiv.rightSlots clauses (SourceOddLists.right clauses e))
    (q : ∀ k, MixedSupport.Projection (a k) (b k))
    (hq : ∀ k, HEq (q k) (SourceAnswerEquiv.slotProjection clauses e k))
    (x : MixedSupport.Assignment a) :
    nativeRightEquiv clauses (SourceOddLists.right clauses e) hb
        (MixedSupport.projectionMap q x) =
      SourceOddLists.projection clauses e
        (nativeLeftEquiv clauses (SourceOddLists.left e) ha x) := by
  subst a
  subst b
  have hprojection : q = SourceAnswerEquiv.slotProjection clauses e := by
    funext k
    exact eq_of_heq (hq k)
  subst q
  exact SourceAnswerEquiv.projection_encode clauses e x

end PerfectCompleteness.NativeLeafAlphabet

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedCardinality
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

end PerfectCompleteness.ProjectedCardinality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_TwoResponseCollisionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

theorem event_of_probability_one (μ : FiniteDistribution Ω) (event : Ω → Bool)
    (hone : μ.probability event = 1) (x : Ω) (hx : μ.weight x ≠ 0) :
    event x = true := by
  by_contra hfalse
  have hle (y : Ω) : (if event y then μ.weight y else 0) ≤ μ.weight y := by
    split
    · exact le_rfl
    · exact μ.nonnegative y
  have hlt : μ.probability event < ∑ y, μ.weight y := by
    unfold FiniteDistribution.probability
    apply Finset.sum_lt_sum (fun y _ => hle y)
    refine ⟨x, Finset.mem_univ _, ?_⟩
    simpa only [ite_eq_right hfalse] using
      lt_of_le_of_ne (μ.nonnegative x) (Ne.symm hx)
  have hbad : (1 : ℝ) < 1 := by simpa only [hone, μ.normalized] using hlt
  exact (lt_irrefl (1 : ℝ)) hbad

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecursiveSamplerLaws
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecordSeedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RecordSeedSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {X R : Type*} [Fintype X] [Fintype R] [DecidableEq R]
  {Seed : R → Type*} [∀ r, Fintype (Seed r)]

theorem probability_eq_table_mean (P : FiniteDistribution X) (record : X → R)
    (kernel : (r : R) → FiniteDistribution (Seed r))
    (event : (x : X) → Seed (record x) → Bool) :
    (freshLaw P record kernel).probability (fun z => event z.1 z.2) =
      (FiniteProduct.law kernel).expectation
        (fun table => P.probability (fun x => event x (table (record x)))) := by
  rw [freshLaw, CompletionSoundness.sigmaLaw_probability]
  calc
    _ = P.expectation (fun x => (FiniteProduct.law kernel).probability
        (fun table => event x (table (record x)))) := by
      apply FiniteDistribution.expectation_congr
      intro x
      have h := FiniteDistribution.probability_pushforward
        (FiniteProduct.law kernel) (fun table => table (record x)) (event x)
      rw [FiniteProduct.eval_pushforward] at h
      exact h
    _ = P.expectation (fun x => (FiniteProduct.law kernel).expectation
        (fun table => if event x (table (record x)) then 1 else 0)) := by
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        mul_ite, mul_one, mul_zero]
    _ = (FiniteProduct.law kernel).expectation (fun table => P.expectation
        (fun x => if event x (table (record x)) then 1 else 0)) :=
      FiniteDistribution.expectation_comm P (FiniteProduct.law kernel) _
    _ = _ := by
      simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
        mul_ite, mul_one, mul_zero]

theorem supported_row (kernel : (r : R) → FiniteDistribution (Seed r))
    (table : (r : R) → Seed r)
    (hs : (FiniteProduct.law kernel).weight table ≠ 0) (r : R) :
    (kernel r).weight (table r) ≠ 0 := by
  intro hr
  exact hs (Finset.prod_eq_zero (Finset.mem_univ r) hr)

theorem probability_supported_guard (P : FiniteDistribution X) (event : X → Bool) :
    P.probability (fun x => decide (P.weight x ≠ 0) && event x) = P.probability event := by
  unfold FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : P.weight x = 0
  · simp only [hx, ne_eq, not_true_eq_false, decide_false, Bool.false_and,
      ite_self]
  · simp only [decide_eq_true hx, Bool.true_and]

theorem probability_le_of_supported_tables (P : FiniteDistribution X) (record : X → R)
    (kernel : (r : R) → FiniteDistribution (Seed r))
    (event : (x : X) → Seed (record x) → Bool) (bound : ℝ)
    (hbound : ∀ table, (FiniteProduct.law kernel).weight table ≠ 0 →
      P.probability (fun x => decide (P.weight x ≠ 0) && event x (table (record x))) ≤ bound) :
    (freshLaw P record kernel).probability (fun z => event z.1 z.2) ≤ bound := by
  rw [probability_eq_table_mean]
  apply DecoderTableAdmissibility.expectation_le_of_support
  intro table hs
  rw [← probability_supported_guard P (fun x => event x (table (record x)))]
  exact hbound table hs

end
end PerfectCompleteness.RecordSeedSampling



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddListExtraction
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RecursiveSpaceEquiv.squareEquiv_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OddListExtraction

open scoped BigOperators Classical
open PointwiseSpaces

variable {X Y A B : Type*}

theorem indicator_comp [Fintype A] (q : X → A) (π : A → B) (b : B) :
    indicator (π ∘ q) b = ∑ a ∈ Finset.univ.filter (fun a => π a = b), indicator q a := by
  classical
  funext x
  simp only [Finset.sum_apply, indicator, Function.comp_apply]
  by_cases hb : π (q x) = b
  · rw [ite_eq_left hb]
    symm
    rw [Finset.sum_eq_single (q x)]
    · simp
    · intro a _ ha
      simp only [ite_eq_right (Ne.symm ha)]
    · intro h
      exact (h (by simp [hb])).elim
  · rw [ite_eq_right hb]
    symm
    apply Finset.sum_eq_zero
    intro a ha
    have hqa : q x ≠ a := by
      intro heq
      exact hb ((congrArg π heq).trans (Finset.mem_filter.mp ha).2)
    exact ite_eq_right hqa

section Projection

variable [Fintype A] [Fintype B]
variable (H : Submodule F2 (X → F2)) (K : Submodule F2 (Y → F2))
variable (q : X → A) (r : Y → B)
variable (hH : ∀ a, indicator q a ∈ H) (hK : ∀ b, indicator r b ∈ K)
variable (p : X → Y) (π : A → B) (hcomm : ∀ x, r (p x) = π (q x))
variable (T : K →ₗ[F2] H) (hT : ∀ (f : K) x, (T f).val x = f.val (p x))

include hcomm hT

omit [Fintype B] in
theorem projected_diagonal
    (z : Module.Dual F2 (squareSpace H)) (F' : K →ₗ[F2] K →ₗ[F2] F2)
    (hagree : ∀ f g, F' f g = multiplicationForm H z (T f) (T g)) (b : B) :
    F' (atom K r hK b) (atom K r hK b) =
      ∑ a ∈ Finset.univ.filter (fun a => π a = b), diagonal H q hH z a := by
  classical
  rw [hagree]
  simp only [multiplicationForm_apply, diagonal, ← map_sum]
  congr 1
  apply Subtype.ext
  funext x
  change (T (atom K r hK b)).val x * (T (atom K r hK b)).val x = _
  simp only [hT, atom, Submodule.coe_sum, Finset.sum_apply, productElement,
    Pi.mul_apply]
  have h := congrFun (indicator_comp q π b) x
  simp only [Finset.sum_apply] at h
  have hidem : ∀ a : A, indicator q a x * indicator q a x = indicator q a x :=
    fun a => congrFun (indicator_mul_self q a) x
  simp only [hidem]
  rw [← h]
  simp only [indicator, Function.comp_apply, hcomm]
  split_ifs <;> simp

theorem projected_support
    (z : Module.Dual F2 (squareSpace H)) (F' : K →ₗ[F2] K →ₗ[F2] F2)
    (hagree : ∀ f g, F' f g = multiplicationForm H z (T f) (T g)) :
    OddLists.support (fun b => F' (atom K r hK b) (atom K r hK b)) =
      OddLists.parityPushforward π (OddLists.support (diagonal H q hH z)) := by
  classical
  rw [OddLists.parityPushforward_support]
  congr 1
  funext b
  rw [projected_diagonal H K q r hH hK p π hcomm T hT z F' hagree b]
  exact Finset.sum_filter _ _

end Projection

private theorem parityPushforward_decidableEq_irrel [Fintype B]
    (d₁ d₂ : DecidableEq B) (π : A → B) (L : Finset A) :
    @OddLists.parityPushforward A B _ d₁ π L =
      @OddLists.parityPushforward A B _ d₂ π L :=
  congrArg (fun d : DecidableEq B => @OddLists.parityPushforward A B _ d π L)
    (Subsingleton.elim d₁ d₂)

theorem source_projected_support {branch : Nat → Nat} {n t : Nat}
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (s : RecursiveSpaces.Slots branch n)
    (z : Module.Dual F2 (squareSpace (TreeSourceSpaces.H slots)))
    (F' : TreeSourceSpaces.H projected →ₗ[F2] TreeSourceSpaces.H projected →ₗ[F2] F2)
    (hagree : ∀ f g, F' f g = multiplicationForm (TreeSourceSpaces.H slots) z
      (TreeSourceSpaces.HPullback p f) (TreeSourceSpaces.HPullback p g)) :
    OddLists.support (fun b => F'
      (atom (TreeSourceSpaces.H projected) (fun x => x s)
        (source_leaf_indicator_mem projected s) b)
      (atom (TreeSourceSpaces.H projected) (fun x => x s)
        (source_leaf_indicator_mem projected s) b)) =
      OddLists.parityPushforward (MixedSupport.projectionMap (p s))
        (OddLists.support (diagonal (TreeSourceSpaces.H slots) (fun x => x s)
          (source_leaf_indicator_mem slots s) z)) := by
  have h := projected_support (TreeSourceSpaces.H slots) (TreeSourceSpaces.H projected)
    (fun x => x s) (fun x => x s) (source_leaf_indicator_mem slots s)
    (source_leaf_indicator_mem projected s) (TreeSourceSpaces.sourceProjection p)
    (MixedSupport.projectionMap (p s)) (fun _ => rfl)
    (TreeSourceSpaces.HPullback p) (fun _ _ => rfl) z F' hagree
  exact h.trans (parityPushforward_decidableEq_irrel _ _ _ _)

end PerfectCompleteness.OddListExtraction

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CutChildCleanLawLemmas
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

theorem coefficient_eq (L : Nat) (branch : Nat → Nat) (height t calls : Nat)
    (rows : Nat → Nat) :
    coefficient L branch height t calls rows =
      (1 - (RepetitionRate.halfRate L : ℝ)) * zeroProbability branch height t calls rows := by
  rw [RepetitionRate.halfRate_cast]
  unfold coefficient
  ring

end
end PerfectCompleteness.ProjectedCleanRate

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceChildKernelLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernelRate

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces ProjectedCardinality

variable {branch : Nat → Nat} {height t v m : Nat} [NeZero m]
  {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)

theorem bound_from_repetition {s L cube : Nat} [NeZero s] (hcube : 0 < cube)
    (repetition : ∀ k, ((SourceOddLists.game s clauses t).repetition k).value ≤
      (RepetitionRate.halfRate L : ℝ) ^ k)
    (event : Sample (C := C) (t := t) rows clauses designated → Bool)
    (strategies : (record : Record (C := C) (t := t) rows clauses designated) →
      Strategy (CleanChildren rows clauses designated record → Fin t → Fin m)
        (CleanChildren rows clauses designated record → Fin t → Fin v)
        (CleanChildren rows clauses designated record → OddLists.OddList s (SourceOddLists.LeftLabels t))
        (CleanChildren rows clauses designated record → OddLists.OddList s (SourceOddLists.RightLabels t)))
    (inclusion : ∀ record x,
      UniformCleanSources.recordEvent (Factors (C := C) (t := t) rows clauses designated)
        (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record x = true →
      event x = true →
      (IndexedRepetition.game (SourceOddLists.game s clauses t)
        (CleanChildren rows clauses designated record)).wins (strategies record)
          (fun i => (x i.val).1) = true) :
    (SourceChildKernel.originalLaw (C := C) (t := t) rows clauses designated
      (fun _ => ProjectedCleanRate.projectionFlag cube hcube)).probability event ≤
      (1 - ProjectedCleanRate.coefficient L branch height t (Fintype.card C) rows /
        (cube : ℝ) ^ 2) ^ (branch height) := by
  let restLaw := fun i : Fin (branch height) => FiniteProduct.law
    (fun _ : {leaf : Slots branch height // leaf ≠ designated i} =>
      SourceOddLists.tupleLaw m t)
  have bound := UniformCleanSoundness.source_soundness
    (Factors (C := C) (t := t) rows clauses designated)
    (SourceOddLists.game s clauses t) restLaw
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)
    (SourceChildKernel.nonprojected (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
    (fun _ => shapeCardinality branch t
      (CleanTreeFactors.height (Fintype.card C) rows)
      (CleanTreeFactors.square (Fintype.card C) rows))
    (fun i source j => factor_card_eq
      (CleanTreeFactors.square (Fintype.card C) rows j)
      (CleanTreeFactors.factorIds (Fintype.card C) rows
        (SourceChildKernel.ids clauses designated i source) j) (fun _ _ => 0))
    event (RepetitionRate.halfRate L : ℝ) repetition strategies inclusion
  have hoccurrences : (SourceOddLists.game s clauses t).occurrences =
      SourceOddLists.tupleLaw m t := rfl
  rw [hoccurrences] at bound
  have hbase :
      1 - (1 - (RepetitionRate.halfRate L : ℝ)) *
        (ProjectedCleanRate.projectionDensity cube *
          ProjectedCleanRate.zeroProbability branch height t (Fintype.card C) rows) =
      1 - ProjectedCleanRate.coefficient L branch height t (Fintype.card C) rows /
        (cube : ℝ) ^ 2 := by
    rw [ProjectedCleanRate.coefficient_eq]
    unfold ProjectedCleanRate.projectionDensity
    ring
  calc
    _ ≤ ∏ _i : Fin (branch height),
        (1 - (1 - (RepetitionRate.halfRate L : ℝ)) *
          (ProjectedCleanRate.projectionDensity cube *
            ProjectedCleanRate.zeroProbability branch height t (Fintype.card C) rows)) := by
      simpa only [SourceChildKernel.originalLaw, SourceChildKernel.childrenLaw, Factors, restLaw,
        ProjectedCleanRate.projectionFlag_true, ProjectedCleanRate.zeroProbability] using bound
    _ = _ := by
      simp only [hbase, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end
end PerfectCompleteness.SourceChildKernelRate

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceLocalOddLists
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceLocalOddLists

open scoped Classical
open PointwiseSpaces TreeSourceSpaces SourceAnswerEquiv
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {h t v m s : Nat}

theorem extract_accepts (positive : 0 < s)
    {slots projected : RecursiveSpaces.Slots branch h → Fin t → MixedSupport.Slot}
    (p : ∀ leaf k, MixedSupport.Projection (slots leaf k) (projected leaf k))
    (leaf : RecursiveSpaces.Slots branch h) (F : Form slots) (F' : Form projected)
    (z : Module.Dual F2 (squareSpace (H slots)))
    (hform : F = OddListExtraction.multiplicationForm (H slots) z)
    (hone : (1 : Domain slots → F2) ∈ squareSpace (H slots))
    (hnorm : z ⟨1, hone⟩ = 1) (hrank : OddListExtraction.formRank (H slots) F ≤ s)
    (hagree : ∀ f g, F' f g = OddListExtraction.multiplicationForm (H slots) z
      (HPullback p f) (HPullback p g))
    (leftFallback : LeafDomain slots leaf) (rightFallback : LeafDomain projected leaf) :
    OddLists.OddList.map (MixedSupport.projectionMap (p leaf))
      (extract positive slots F leaf leftFallback) =
      extract positive projected F' leaf rightFallback := by
  have hleft : Odd (leafSupport slots F leaf).card ∧ (leafSupport slots F leaf).card ≤ s := by
    rw [hform] at hrank ⊢
    exact (OddListExtraction.extractedList (H slots) (fun x => x leaf)
      (OddListExtraction.source_leaf_indicator_mem slots leaf) z hone hnorm s hrank).property
  have hsupport : leafSupport projected F' leaf =
      OddLists.parityPushforward (MixedSupport.projectionMap (p leaf)) (leafSupport slots F leaf) := by
    rw [hform]
    exact OddListExtraction.source_projected_support p leaf z F' hagree
  have hright : Odd (leafSupport projected F' leaf).card ∧
      (leafSupport projected F' leaf).card ≤ s := by
    rw [hsupport]
    exact ⟨OddLists.parityPushforward_odd _ _ hleft.1,
      (OddLists.parityPushforward_card_le _ _).trans hleft.2⟩
  apply Subtype.ext
  rw [OddLists.OddList.map_val]
  change OddLists.parityPushforward (MixedSupport.projectionMap (p leaf))
      (OddLists.OddList.extract positive leftFallback (leafSupport slots F leaf)).val =
    (OddLists.OddList.extract positive rightFallback (leafSupport projected F' leaf)).val
  rw [OddLists.OddList.extract_valid positive leftFallback _ hleft,
    OddLists.OddList.extract_valid positive rightFallback _ hright]
  exact hsupport.symm

end
end PerfectCompleteness.SourceLocalOddLists

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionAssembly
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanEndpointProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanEndpointProjection

open scoped Classical
open RecursiveSpaces MixedSupport SourceQuestionReconstruction

noncomputable section

private theorem dite_heq_of_pos {α β : Type} {P : Prop} [Decidable P]
    (f : P → α) (g : ¬ P → α) (b : β) (hP : P)
    (h : HEq (f hP) b) : HEq (dite P f g) b := by
  rw [dite_eq_left hP]
  exact h

variable {v m t : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)

theorem sourceProjection_of_true (projected : Bool)
    (e : SourceOddLists.Occurrences m t) (k : Fin t) (hp : projected = true) :
    HEq (sourceProjection clauses projected e k)
      (SourceAnswerEquiv.slotProjection clauses e k) := by
  subst projected
  rfl

variable {branch : Nat → Nat} {h : Nat}
  (designated : Fin (branch h) → Slots branch h)
  (clean : Fin (branch h) → Prop)
  (visible : Visible (E := SourceTuple m t) designated clean)

variable (projected : Fin (branch h) → Bool)

theorem insideProjection_designated
    (cleanProjected : ∀ i, clean i → projected i = true)
    (e : {i : Fin (branch h) // clean i} → SourceOddLists.Occurrences m t)
    (i : {i : Fin (branch h) // clean i}) (k : Fin t) :
    HEq (insideProjection clauses designated clean visible projected cleanProjected e
        (i.val, designated i.val) k)
      (SourceAnswerEquiv.slotProjection clauses (e i) k) := by
  refine @dite_heq_of_pos _ _
    (clean i.val ∧ designated i.val = designated i.val) _ _ _
    (SourceAnswerEquiv.slotProjection clauses (e i) k) ⟨i.property, rfl⟩ ?_
  exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
    (sourceProjection_of_true clauses (projected i.val) (e i) k
      (cleanProjected i.val i.property))

end
end PerfectCompleteness.CleanEndpointProjection

end

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanLeftDecoderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanLeftDecoder

noncomputable section

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  (E : Exposed branch rows repeats n h t v m)

variable (upper : Nodes branch n) (lowerLevel : Nat)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : Useful E upper lowerLevel)

local instance rowSpaceFintype_rcd8717_1 (own : Own E) (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace (slots E own) node) := Fintype.ofFinite _
local instance nodeSpaceFintype_rcd8717_1 (own : Own E) (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH (slots E own) node) := Fintype.ofFinite _
theorem supported_row (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (seed : Seed E upper)
    (hsupport : (seedLaw E upper lowerLevel σ useful r ρ A).weight seed ≠ 0)
    (own : Own E) : (law E upper lowerLevel σ useful r ρ A own).weight (seed own) ≠ 0 := by
  intro hz
  apply hsupport
  change (∏ q, (law E upper lowerLevel σ useful r ρ A q).weight (seed q)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ own) hz

variable (hbranch : ∀ k < n, 0 < branch k)

theorem law_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (own : Own E) :
    (law E upper lowerLevel σ useful r ρ A own).probability
      (fun q => decide (HierarchicalLeftDecoder.Valid (slots E own) upper lowerLevel
        hbranch (background E upper own) q)) = 1 :=
  HierarchicalLeftDecoder.adviceLaw_valid (slots E own) upper lowerLevel hbranch
    (background E upper own) σ (useful own) r ρ hρ
    (advice E upper lowerLevel r A own).1 (advice E upper lowerLevel r A own).2

theorem supported_seed_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (seed : Seed E upper)
    (hsupport : (seedLaw E upper lowerLevel σ useful r ρ A).weight seed ≠ 0)
    (own : Own E) :
    HierarchicalLeftDecoder.Valid (slots E own) upper lowerLevel hbranch
      (background E upper own) (seed own) := by
  exact of_decide_eq_true (DecoderTableAdmissibility.event_of_probability_one
    (law E upper lowerLevel σ useful r ρ A own)
    (fun q => decide (HierarchicalLeftDecoder.Valid (slots E own) upper lowerLevel
      hbranch (background E upper own) q))
    (law_valid E upper lowerLevel σ useful hbranch r ρ hρ A own) (seed own)
    (supported_row E upper lowerLevel σ useful r ρ A seed hsupport own))

theorem supported_output_normalized (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r) (seed : Seed E upper)
    (hsupport : (seedLaw E upper lowerLevel σ useful r ρ A).weight seed ≠ 0)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (own : Own E) :
    output E upper lowerLevel hbranch d own (seed own)
      (HierarchicalLeftDecoder.lowerOne (slots E own) upper lowerLevel hbranch d) = 1 :=
  (supported_seed_valid E upper lowerLevel σ useful hbranch r ρ hρ A seed hsupport own d).1

end
end PerfectCompleteness.CleanLeftDecoder

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OddListAlphabetTransport
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OddLists

open scoped BigOperators Classical

noncomputable section

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
  [DecidableEq A] [DecidableEq B] [DecidableEq C]

private theorem parityPushforward_comp (π : A → B) (ρ : B → C) (L : Finset A) :
    parityPushforward ρ (parityPushforward π L) =
      parityPushforward (ρ ∘ π) L := by
  let f : A → ZMod 2 := fun a => if a ∈ L then 1 else 0
  have hf : support f = L := by
    ext a
    by_cases ha : a ∈ L <;> simp [mem_support, f, ha]
  rw [← hf, parityPushforward_support, parityPushforward_support,
    parityPushforward_support]
  apply congrArg (fun g : C → ZMod 2 => support g)
  funext c
  calc
    (∑ b, if ρ b = c then ∑ a, if π a = b then f a else 0 else 0) =
        ∑ b, ∑ a, if ρ b = c then (if π a = b then f a else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : ρ b = c <;> simp only [hb, ite_true, if_true, ite_false, if_false, Finset.sum_const_zero]
    _ = ∑ a, ∑ b, if ρ b = c then (if π a = b then f a else 0) else 0 :=
      Finset.sum_comm
    _ = ∑ a, if (ρ ∘ π) a = c then f a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single (π a)]
      · simp only [Function.comp_apply, ite_true, if_true]
      · intro b _ hb
        simp only [ite_eq_right (Ne.symm hb), ite_self]
      · intro h
        exact (h (Finset.mem_univ _)).elim

namespace OddList

theorem map_comp {s : Nat} (π : A → B) (ρ : B → C) (L : OddList s A) :
    map ρ (map π L) = map (ρ ∘ π) L := by
  apply Subtype.ext
  exact parityPushforward_comp π ρ L.val

theorem map_commutes {D : Type*} [Fintype D] [DecidableEq D] {s : Nat}
    (π : A → B) (α : A → C) (β : B → D) (ρ : C → D)
    (h : ∀ a, ρ (α a) = β (π a))
    (L : OddList s A) (R : OddList s B) (hnative : map π L = R) :
    map ρ (map α L) = map β R := by
  rw [map_comp α ρ L, show ρ ∘ α = β ∘ π from funext h,
    ← map_comp π β L, hnative]

end OddList

end
end PerfectCompleteness.OddLists

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderOddLists
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderOddLists

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open ChildBlockProjection CleanDecoderContext
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m s : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (E : Exposed branch rows repeats n h t v m upper d)

theorem nativeProjection_designated (e : Occurrences E) (i : CleanChildren E) (k : Fin t) :
    HEq (nodeProjection (fullProjection E e) (lower E) (designatedLeaf E i) k)
      (SourceAnswerEquiv.slotProjection E.clauses (e i) k) := by
  have hcut := (CutProjectionAssembly.fillProjection_at_cut (path E) E.outside
    (CleanEndpointSlots.leftInside E.clauses E.designated E.clean E.visible (leftQuestions E e))
    (CleanEndpointSlots.rightInside E.clauses E.designated E.clean E.visible E.projected
      (rightQuestions E e))
    (CleanEndpointProjection.insideProjection E.clauses E.designated E.clean E.visible
      E.projected E.cleanProjected e)
    (i.val, E.designated i.val) k).trans
      (CleanEndpointProjection.insideProjection_designated E.clauses E.designated E.clean
        E.visible E.projected E.cleanProjected e i k)
  exact Eq.mpr (congrArg (fun leaf : Slots branch n =>
    HEq (fullProjection E e leaf k) (SourceAnswerEquiv.slotProjection E.clauses (e i) k))
    (nativeLeaf_embedding E (i.val, E.designated i.val))) hcut

theorem projection_encode (e : Occurrences E) (i : CleanChildren E)
    (x : LeafDomain (leftNative E (leftQuestions E e)) (designatedLeaf E i)) :
    rightEncoding E (rightQuestions E e) i
        (MixedSupport.projectionMap
          (nodeProjection (fullProjection E e) (lower E) (designatedLeaf E i)) x) =
      SourceOddLists.projection E.clauses (e i)
        (leftEncoding E (leftQuestions E e) i x) :=
  NativeLeafAlphabet.projection_encode E.clauses (e i)
    (leftNative_designated E (leftQuestions E e) i)
    (rightNative_designated E (rightQuestions E e) i) _
    (nativeProjection_designated E e i) x

variable (hbranch : ∀ k < n, 0 < branch k)

theorem forms_agree (leftSeed : LeftSeed E) (rightSeed : RightSeed E)
    (e : Occurrences E) (htarget : rightSeed (rightQuestions E e) = target E leftSeed e)
    (f g : H (rightNative E (rightQuestions E e))) :
    rightForm E hbranch rightSeed (rightQuestions E e) f g =
      OddListExtraction.multiplicationForm (H (leftNative E (leftQuestions E e)))
        (leftOutput E hbranch leftSeed (leftQuestions E e))
        (HPullback (nodeProjection (fullProjection E e) (lower E)) f)
        (HPullback (nodeProjection (fullProjection E e) (lower E)) g) := by
  change RightDecoderDescendant.form (rightSlots E (rightQuestions E e)) upper (lower E)
    E.cut (DecoderSourcePullback.upperBranch upper hbranch)
      (rightSeed (rightQuestions E e)) f g = _
  rw [htarget]
  exact DecoderSourcePullback.form_upperTarget (fullProjection E e) upper (h + 1)
    hbranch d E.cut (leftSeed (leftQuestions E e)) f g

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : CleanLeftDecoder.Useful (leftExposed E) upper (h + 1))

theorem responses_accept (positive : 0 < s) (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (leftSeed : LeftSeed E)
    (hsupport : (CleanLeftDecoder.seedLaw (leftExposed E) upper (h + 1)
      σ useful r ρ A).weight leftSeed ≠ 0)
    (rightSeed : RightSeed E) (e : Occurrences E)
    (htarget : rightSeed (rightQuestions E e) = target E leftSeed e)
    (hrank : OddListExtraction.formRank (H (leftNative E (leftQuestions E e)))
      (leftForm E hbranch leftSeed (leftQuestions E e)) ≤ s)
    (i : CleanChildren E) :
    OddLists.OddList.map (SourceOddLists.projection E.clauses (e i))
      (leftResponse E hbranch positive leftSeed (leftQuestions E e) i) =
      rightResponse E hbranch positive rightSeed (rightQuestions E e) i := by
  have hnorm := CleanLeftDecoder.supported_output_normalized (leftExposed E) upper (h + 1)
    σ useful hbranch r ρ hρ A leftSeed hsupport d (leftQuestions E e)
  have hnative := SourceLocalOddLists.extract_accepts positive
    (nodeProjection (fullProjection E e) (lower E)) (designatedLeaf E i)
    (leftForm E hbranch leftSeed (leftQuestions E e))
    (rightForm E hbranch rightSeed (rightQuestions E e))
    (leftOutput E hbranch leftSeed (leftQuestions E e)) rfl
    (HierarchicalLeftDecoder.lowerOne (leftSlots E (leftQuestions E e)) upper (h + 1)
      hbranch d).property hnorm hrank (forms_agree E hbranch leftSeed rightSeed e htarget)
    ((leftEncoding E (leftQuestions E e) i).symm (fun _ => 0))
    ((rightEncoding E (rightQuestions E e) i).symm (fun _ => false))
  exact OddLists.OddList.map_commutes _ (leftEncoding E (leftQuestions E e) i)
    (rightEncoding E (rightQuestions E e) i) (SourceOddLists.projection E.clauses (e i))
    (fun x => (projection_encode E e i x).symm) _ _ hnative

end
end PerfectCompleteness.CleanDecoderOddLists

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderSeedLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
theorem supported_left (seed : Seed E)
    (hs : (seedLaw E σ useful r ρ A W a threshold).weight seed ≠ 0) :
    (leftSeedLaw E σ useful r ρ A).weight seed.1 ≠ 0 := by
  intro hz
  apply hs
  change (leftSeedLaw E σ useful r ρ A).weight seed.1 *
    (rightSeedLaw E σ W a threshold).weight seed.2 = 0
  rw [hz, zero_mul]

end
end PerfectCompleteness.CleanDecoderSeedLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CleanDecoderRateLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.RoundTables.instNonemptyFinDartsValTableLtNatOfNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanDecoderRate

noncomputable section

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : Setup branch rows repeats n h t v m upper d)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (record : Record S) →
    CleanLeftDecoder.Useful (CleanDecoderContext.leftExposed (context S record)) upper (h + 1))
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (W : Submodule F2 (OwnInputReference.UpperVector rows upper))
  (a : OwnInputReference.LowerVector rows (HierarchicalLeftDecoder.LowerNode upper (h + 1) d))
  (threshold : ℝ)

variable (hbranch : ∀ k < n, 0 < branch k)

theorem bound_oai {s L cube : Nat} [NeZero s] (hcube : 0 < cube) (hρ : 0 < ρ)
    (repetition : ∀ k, ((SourceOddLists.game s S.clauses t).repetition k).value ≤
      (RepetitionRate.halfRate L : ℝ) ^ k) :
    (law S σ useful r ρ A W a threshold cube hcube).probability
        (fun z => agrees S hbranch s z.1 z.2) ≤
      (1 - ProjectedCleanRate.coefficient L branch h t (Fintype.card (Calls S)) rows /
        (cube : ℝ) ^ 2) ^ (branch h) := by
  unfold law
  apply RecordSeedSampling.probability_le_of_supported_tables
  intro table htable
  let strategies := fun record : Record S =>
    CleanDecoderOddLists.strategy (context S record) hbranch (Nat.pos_of_neZero s)
      (table record).1 (table record).2
  apply SourceChildKernelRate.bound_from_repetition rows S.clauses S.designated
    hcube repetition _ strategies
  intro record x hevent heventSeed
  have hrecord : observations S x = record := by
    apply of_decide_eq_true
    exact (CleanRecordObservation.event_eq rows S.clauses S.designated record x).symm.trans hevent
  subst record
  have hseed := RecordSeedSampling.supported_row
    (kernel S σ useful r ρ A W a threshold) table htable (observations S x)
  have hleft := CleanDecoderSeedLaw.supported_left (context S (observations S x))
    σ (useful (observations S x)) r ρ A W a threshold
    (table (observations S x)) hseed
  have hagrees : agrees S hbranch s x (table (observations S x)) = true :=
    (Bool.and_eq_true_iff.mp heventSeed).2
  have hactual := of_decide_eq_true hagrees
  simp only [OccurrenceGame.wins, IndexedRepetition.game, SourceOddLists.game,
    OddListGame.game, OccurrenceGame.ofProjection, strategies,
    CleanDecoderOddLists.strategy, decide_eq_true_eq]
  intro i
  exact CleanDecoderOddLists.responses_accept (context S (observations S x)) hbranch
    σ (useful (observations S x)) (Nat.pos_of_neZero s) r ρ hρ A
    (table (observations S x)).1 hleft (table (observations S x)).2
    (sources S (observations S x) x) hactual.2 hactual.1 i

end
end PerfectCompleteness.CleanDecoderRate

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.CleanDecoderRate.bound_oai := @OAI.PerfectCompleteness.CleanDecoderRate.bound_oai
