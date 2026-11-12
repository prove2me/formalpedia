-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalAdviceFamily.reference_I_mass_ge
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:17:38.92871+00:00
-- url     : https://prove2.me/submissions/99f31142-0700-48d8-8c5f-7c79d788cfde

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
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

theorem probability_inter_eq_mul_conditional (μ : FiniteDistribution Ω)
    (given event : Ω → Bool) (positive : 0 < μ.probability given) :
    μ.probability (fun x => given x && event x) =
      μ.probability given * (μ.condition given positive).probability event := by
  have h := (eq_div_iff (ne_of_gt positive)).mp
    (μ.probability_condition given event positive)
  simpa only [mul_comm] using h.symm

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TupleIndexEmitterLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.UsefulMark

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω P : Type*} [Fintype Ω] [Fintype P]

theorem probability_eq_sum_fibers (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : Ω → Bool) : μ.probability event = ∑ z, lowerFiberMass μ p event z := by
  unfold lowerFiberMass FiniteDistribution.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x <;> simp [he, eq_comm]

end
end PerfectCompleteness.UsefulMark



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerReplayTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
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

theorem uniform_probability_equiv (e : Ω ≃ Γ) (event : Γ → Bool) :
    (FiniteDistribution.uniform Ω).probability (fun x => event (e x)) =
      (FiniteDistribution.uniform Γ).probability event := by
  rw [← uniform_transport e, FiniteDistribution.probability_transport]

theorem uniform_probability (T : Ω → Prop) :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) =
      (Fintype.card {x : Ω // T x} : ℝ) / (Fintype.card Ω : ℝ) := by
  calc
    _ = (∑ x : Ω, if T x then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := by
      change (∑ x : Ω, if decide (T x) then 1 / (Fintype.card Ω : ℝ) else 0) = _
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : T x <;> simp [hx]
    _ = _ := by simp only [Fintype.card_subtype, Finset.sum_boole]

theorem uniform_probability_pos (T : Ω → Prop) [Nonempty {x : Ω // T x}] :
    0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) := by
  rw [uniform_probability]
  exact div_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)

omit [Nonempty Ω] in
theorem uniform_subtype_pushforward_weight (T : Ω → Prop)
    [Nonempty {x : Ω // T x}] (x : Ω) :
    ((FiniteDistribution.uniform {x : Ω // T x}).pushforward Subtype.val).weight x =
      if T x then 1 / (Fintype.card {x : Ω // T x} : ℝ) else 0 := by
  change (∑ y : {x : Ω // T x},
    if y.val = x then 1 / (Fintype.card {x : Ω // T x} : ℝ) else 0) = _
  by_cases hx : T x
  · rw [ite_eq_left hx]
    rw [Finset.sum_eq_single (⟨x, hx⟩ : {x : Ω // T x})]
    · simp
    · intro y _ hy
      have hne : y.val ≠ x := fun heq => hy (Subtype.ext heq)
      simp [hne]
    · simp
  · rw [ite_eq_right hx]
    apply Finset.sum_eq_zero
    intro y _
    have hne : y.val ≠ x := fun heq => hx (heq ▸ y.property)
    simp [hne]

theorem condition_uniform (T : Ω → Prop) [Nonempty {x : Ω // T x}]
    (positive : 0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x))) :
    (FiniteDistribution.uniform Ω).condition (fun x => decide (T x)) positive =
      (FiniteDistribution.uniform {x : Ω // T x}).pushforward Subtype.val := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  rw [uniform_subtype_pushforward_weight]
  change (if decide (T x) then
    (1 / (Fintype.card Ω : ℝ)) /
      (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)) else 0) = _
  rw [uniform_probability]
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  by_cases hx : T x
  · simpa [hx] using
      div_div_div_cancel_right₀ hcard (1 : ℝ) (Fintype.card {x : Ω // T x} : ℝ)
  · simp [hx]

theorem probability_condition_uniform (T : Ω → Prop) [Nonempty {x : Ω // T x}]
    (positive : 0 < (FiniteDistribution.uniform Ω).probability (fun x => decide (T x)))
    (event : Ω → Bool) :
    ((FiniteDistribution.uniform Ω).condition (fun x => decide (T x)) positive).probability
        event =
      (FiniteDistribution.uniform {x : Ω // T x}).probability (fun x => event x.val) := by
  rw [condition_uniform, FiniteDistribution.probability_pushforward]

end
end PerfectCompleteness.UniformConditioning

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GoodAdviceEventsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.GoodAdviceEvents

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.ManyGoodRows PerfectCompleteness.GoodRowSampling

attribute [local instance] linearMapFintype

section FiniteLaws

variable {Ω P : Type*} [Fintype Ω] [Fintype P] [Nonempty Ω]

omit [Fintype P] [Nonempty Ω] in
theorem adapted_fiber_probability (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : P → Ω → Bool) (z : P) :
    UsefulMark.lowerFiberMass μ p (fun x => event (p x) x) z =
      μ.probability (fun x => decide (p x = z) && event z x) := by
  unfold UsefulMark.lowerFiberMass
  congr 1
  funext x
  by_cases hx : p x = z <;> simp [hx]

omit [Fintype P] in
theorem adapted_uniform_fiber_probability (p : Ω → P)
    (event : P → Ω → Bool) (z : P) [Nonempty {x : Ω // p x = z}] :
    UsefulMark.lowerFiberMass (FiniteDistribution.uniform Ω) p
        (fun x => event (p x) x) z =
      (FiniteDistribution.uniform Ω).probability (fun x => decide (p x = z)) *
        (FiniteDistribution.uniform {x : Ω // p x = z}).probability
          (fun x => event z x.val) := by
  rw [adapted_fiber_probability]
  rw [FiniteDistribution.probability_inter_eq_mul_conditional _ _ _
    (UniformConditioning.uniform_probability_pos (fun x => p x = z))]
  rw [UniformConditioning.probability_condition_uniform]

omit [Fintype P] [Nonempty Ω] in
theorem adapted_fiber_probability_zero (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : P → Ω → Bool) (z : P) (h : ∀ x, event z x = false) :
    UsefulMark.lowerFiberMass μ p (fun x => event (p x) x) z = 0 := by
  rw [adapted_fiber_probability]
  simp only [h, Bool.and_false, FiniteDistribution.probability_false]

theorem uniform_probability_eq_expect (event : Ω → Bool) :
    (FiniteDistribution.uniform Ω).probability event =
      𝔼 x : Ω, if event x then (1 : ℝ) else 0 := by
  have h : (FiniteDistribution.uniform Ω).probability event =
      (FiniteDistribution.uniform Ω).expectation
        (fun x => if event x then (1 : ℝ) else 0) := by
    simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
      mul_ite, mul_one, mul_zero]
  rw [h, FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

omit [Nonempty Ω] in
theorem product_probability {Γ : Type*} [Fintype Γ]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (event : Ω × Γ → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun x => ν.probability (fun y => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

end FiniteLaws

variable {E F Y : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype E] [Fintype F] [Fintype Y]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem witness_agreement_probability {f : (E →ₗ[F2] F) → Option Y}
    {r : Nat} {ρ : ℝ} {A : RowMap F r} {U : E →ₗ[F2] (Fin r → F2)}
    (w : Witness f r ρ A U) :
    letI : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
    ρ * (FiniteDistribution.uniform (RowFiber A U)).probability
        (fun X => decide (X.val.domRestrict w.columnSpace =
          w.base.domRestrict w.columnSpace)) ≤
      (FiniteDistribution.uniform (RowFiber A U)).probability
        (fun X => decide (X.val.domRestrict w.columnSpace =
          w.base.domRestrict w.columnSpace ∧ f X.val = some w.value)) := by
  let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
  let S₀ := MatrixSlice.Slice (⊥ : Submodule F2 E) (LinearMap.ker A) w.base
  let S := MatrixSlice.Slice w.columnSpace (LinearMap.ker A) w.base
  let column : S₀ → Prop :=
    fun X => X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace
  let matchValue : S₀ → Bool := fun X => decide (f X.val = some w.value)
  let : Nonempty {X : S₀ // column X} :=
    ⟨⟨⟨w.base, rfl, rfl⟩, rfl⟩⟩
  have column_decide : (fun X => decide (column X)) =
      (fun X => @decide (column X) (Classical.propDecidable _)) := by
    funext sample
    exact decide_eq_decide.mpr Iff.rfl
  have positive : 0 < (FiniteDistribution.uniform S₀).probability
      (fun X => decide (column X)) := by
    rw [column_decide]
    exact UniformConditioning.uniform_probability_pos column
  have density :
      ρ ≤ (FiniteDistribution.uniform S).probability
        (fun X => decide (f X.val = some w.value)) := by
    calc
      ρ ≤ (𝔼 X : S, PartialTableInverse.indicator f w.value X.val) := w.density
      _ = (FiniteDistribution.uniform S).probability
          (fun X => decide (f X.val = some w.value)) := by
        rw [uniform_probability_eq_expect]
        simp only [PartialTableInverse.indicator, decide_eq_true_eq]
  have conditional :
      ρ ≤ ((FiniteDistribution.uniform S₀).condition
        (fun X => decide (column X)) positive).probability matchValue := by
    simp only [column_decide]
    rw [UniformConditioning.probability_condition_uniform]
    have he := UniformConditioning.uniform_probability_equiv
      (SliceMass.columnEventEquivSlice w.columnSpace (LinearMap.ker A) w.base)
      (fun X : S => decide (f X.val = some w.value))
    convert density.trans_eq he.symm using 1
    all_goals try with_reducible_and_instances rfl
    congr!
  have rowSlice :
      ρ * (FiniteDistribution.uniform S₀).probability
          (fun X => decide (column X)) ≤
        (FiniteDistribution.uniform S₀).probability
          (fun X => decide (column X) && matchValue X) := by
    rw [FiniteDistribution.probability_inter_eq_mul_conditional _ _ _ positive]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left conditional
      ((FiniteDistribution.uniform S₀).probability_nonnegative
        (fun X => decide (column X)))
  have hcolumn := UniformConditioning.uniform_probability_equiv
    (rowFiberEquiv A U w.base w.row_value)
    (fun X : RowFiber A U => decide (X.val.domRestrict w.columnSpace =
      w.base.domRestrict w.columnSpace))
  have hmatch := UniformConditioning.uniform_probability_equiv
    (rowFiberEquiv A U w.base w.row_value)
    (fun X : RowFiber A U =>
      decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace) &&
        decide (f X.val = some w.value))
  have hand : (fun X : RowFiber A U =>
      decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace ∧
        f X.val = some w.value)) =
      (fun X : RowFiber A U =>
        decide (X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace) &&
          decide (f X.val = some w.value)) := by
    funext X
    by_cases hcolumn : X.val.domRestrict w.columnSpace = w.base.domRestrict w.columnSpace <;>
      by_cases hvalue : f X.val = some w.value <;> simp [hcolumn, hvalue]
  rw [hand]
  rw [← hcolumn, ← hmatch]
  exact rowSlice

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem I_probability_fixed_row (f : (E →ₗ[F2] F) → Option Y)
    (r : Nat) (ρ : ℝ) (A : RowMap F r) :
    ρ * (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
        (fun X => J f r ρ (A, X)) ≤
      (FiniteDistribution.uniform (E →ₗ[F2] F)).probability
        (fun X => I f r ρ (A, X)) := by
  let μ := FiniteDistribution.uniform (E →ₗ[F2] F)
  let p : (E →ₗ[F2] F) → (E →ₗ[F2] (Fin r → F2)) := fun X => A.comp X
  rw [UsefulMark.probability_eq_sum_fibers μ p,
    UsefulMark.probability_eq_sum_fibers μ p, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro U _
  by_cases hgood : GoodRow f r ρ A U
  · let w := selectWitness f r ρ A U hgood
    let : Nonempty (RowFiber A U) := witness_rowFiber_nonempty w
    have hJ : UsefulMark.lowerFiberMass μ p (fun X => J f r ρ (A, X)) U =
        μ.probability (fun X => @decide (A.comp X = U) (Classical.propDecidable _)) *
          (FiniteDistribution.uniform (RowFiber A U)).probability
            (fun X => decide (X.val.domRestrict w.columnSpace =
              w.base.domRestrict w.columnSpace)) := by
      change UsefulMark.lowerFiberMass (FiniteDistribution.uniform (E →ₗ[F2] F)) p
        (fun X => selectedColumn f r ρ A (p X) X) U = _
      refine (adapted_uniform_fiber_probability p (selectedColumn f r ρ A) U).trans ?_
      simp only [selectedColumn, dite_eq_left hgood]
      congr!
    have hI : UsefulMark.lowerFiberMass μ p (fun X => I f r ρ (A, X)) U =
        μ.probability (fun X => @decide (A.comp X = U) (Classical.propDecidable _)) *
          (FiniteDistribution.uniform (RowFiber A U)).probability
            (fun X => decide (X.val.domRestrict w.columnSpace =
              w.base.domRestrict w.columnSpace ∧ f X.val = some w.value)) := by
      change UsefulMark.lowerFiberMass (FiniteDistribution.uniform (E →ₗ[F2] F)) p
        (fun X => selectedAgreement f r ρ A (p X) X) U = _
      refine (adapted_uniform_fiber_probability p (selectedAgreement f r ρ A) U).trans ?_
      simp only [selectedAgreement, dite_eq_left hgood]
      congr!
    rw [hJ, hI]
    simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
      (witness_agreement_probability w) (μ.probability_nonnegative _)
  · have hJ : UsefulMark.lowerFiberMass μ p (fun X => J f r ρ (A, X)) U = 0 :=
      adapted_fiber_probability_zero μ p (selectedColumn f r ρ A) U
        (by intro X; simp [selectedColumn, hgood])
    rw [hJ, mul_zero]
    exact μ.probability_nonnegative _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Fintype Y] in
theorem I_probability_ge (f : (E →ₗ[F2] F) → Option Y) (r : Nat) (ρ : ℝ) :
    ρ * (law E F r).probability (J f r ρ) ≤
      (law E F r).probability (I f r ρ) := by
  simp only [law, product_probability, FiniteDistribution.expectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
    (I_probability_fixed_row f r ρ A)
    ((FiniteDistribution.uniform (RowMap F r)).nonnegative A)

end
end PerfectCompleteness.GoodAdviceEvents



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HeterogeneousAdviceFamily
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HeterogeneousAdviceFamily

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.ManyGoodRows

attribute [local instance] linearMapFintype

variable {P : Type*} [Fintype P] {E F Y : P → Type*}
  [∀ p, AddCommGroup (E p)] [∀ p, Module F2 (E p)]
  [∀ p, FiniteDimensional F2 (E p)] [∀ p, Fintype (E p)]
  [∀ p, AddCommGroup (F p)] [∀ p, Module F2 (F p)]
  [∀ p, FiniteDimensional F2 (F p)] [∀ p, Fintype (F p)]
  [∀ p, Fintype (Y p)]

omit [∀ p, FiniteDimensional F2 (E p)] [∀ p, FiniteDimensional F2 (F p)]
  [∀ p, Fintype (Y p)] in
theorem J_probability_eq_mean (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    (law (E := E) (F := F) μ r).probability (J f r ρ) =
      μ.expectation (fun p =>
        (GoodAdviceEvents.law (E p) (F p) r).probability (GoodAdviceEvents.J (f p) r ρ)) :=
  CompletionSoundness.sigmaLaw_probability μ
    (fun p => GoodAdviceEvents.law (E p) (F p) r) (J f r ρ)

omit [∀ p, FiniteDimensional F2 (E p)] [∀ p, FiniteDimensional F2 (F p)]
  [∀ p, Fintype (Y p)] in
theorem I_probability_eq_mean (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    (law (E := E) (F := F) μ r).probability (I f r ρ) =
      μ.expectation (fun p =>
        (GoodAdviceEvents.law (E p) (F p) r).probability (GoodAdviceEvents.I (f p) r ρ)) :=
  CompletionSoundness.sigmaLaw_probability μ
    (fun p => GoodAdviceEvents.law (E p) (F p) r) (I f r ρ)

omit [∀ p, FiniteDimensional F2 (E p)] [∀ p, FiniteDimensional F2 (F p)]
  [∀ p, Fintype (Y p)] in
theorem I_probability_ge (μ : FiniteDistribution P)
    (f : (p : P) → (E p →ₗ[F2] F p) → Option (Y p)) (r : Nat) (ρ : ℝ) :
    ρ * (law (E := E) (F := F) μ r).probability (J f r ρ) ≤
      (law (E := E) (F := F) μ r).probability (I f r ρ) := by
  rw [J_probability_eq_mean, I_probability_eq_mean]
  simp only [FiniteDistribution.expectation, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  simpa only [mul_left_comm] using mul_le_mul_of_nonneg_left
    (GoodAdviceEvents.I_probability_ge (f p) r ρ) (μ.nonnegative p)

end
end PerfectCompleteness.HeterogeneousAdviceFamily

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalAdviceExperimentLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalAdviceFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Fourier.MatrixLevelBridge

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.backgroundFiberFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.inputFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.valueFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.coarseFintype
omit [Fintype O] in
theorem reference_J (κ : ℝ) (r : Nat) (ρ : ℝ) (x : ReferenceSample S r) :
    J S κ r ρ (referenceObserve S r x) =
      HeterogeneousAdviceFamily.J (table S κ) r ρ x := rfl

omit [Fintype O] in
theorem reference_I (κ : ℝ) (r : Nat) (ρ : ℝ) (x : ReferenceSample S r) :
    I S κ r ρ (referenceObserve S r x) =
      HeterogeneousAdviceFamily.I (table S κ) r ρ x := rfl

theorem reference_I_mass_ge_oai (κ : ℝ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (r : Nat) (ρ : ℝ) :
    ρ * (referenceLaw S outer backgrounds r).probability
        (fun x => J S κ r ρ (referenceObserve S r x)) ≤
      (referenceLaw S outer backgrounds r).probability
        (fun x => I S κ r ρ (referenceObserve S r x)) := by
  have hJ : (fun x => J S κ r ρ (referenceObserve S r x)) =
      HeterogeneousAdviceFamily.J (table S κ) r ρ := by
    funext x
    exact reference_J S κ r ρ x
  have hI : (fun x => I S κ r ρ (referenceObserve S r x)) =
      HeterogeneousAdviceFamily.I (table S κ) r ρ := by
    funext x
    exact reference_I S κ r ρ x
  rw [hJ, hI]
  exact HeterogeneousAdviceFamily.I_probability_ge
    (backgroundLaw S outer backgrounds) (table S κ) r ρ

end
end PerfectCompleteness.HierarchicalAdviceFamily


end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PerfectCompleteness.HierarchicalAdviceFamily.reference_I_mass_ge_oai.{u_1, u_2} := @OAI.PerfectCompleteness.HierarchicalAdviceFamily.reference_I_mass_ge_oai.{u_1, u_2}
