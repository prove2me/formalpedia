-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:56.484125+00:00
-- url     : https://prove2.me/submissions/72633bc4-8992-44b5-927b-014c46afa910

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
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalProjectedRawPrediction_given_eq_jointEvent
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalProjectedRawPrediction_rawPrediction_eq

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.probability_condition_given _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputAffineSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputAffineSlice

noncomputable section

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

section FiniteLaws

variable {A B T : Type*} [Fintype A] [Fintype B] [Fintype T]

theorem condition_product_hidden (μ : FiniteDistribution A) (ν : FiniteDistribution B)
    (g : A → T) (slice : T → Bool) (visible : B → Bool)
    (positive : 0 < (μ.product ν).probability
      (fun x => slice (g x.1) && visible x.2)) :
    ((μ.product ν).condition (fun x => slice (g x.1) && visible x.2) positive).pushforward
        (fun x => g x.1) =
      (μ.pushforward g).condition slice (product_slice_positive μ ν g slice visible positive) := by
  have hv : ν.probability visible ≠ 0 := by
    intro hv
    have hp := positive
    rw [probability_product_and μ ν (fun h : A => slice (g h)) visible, hv, mul_zero] at hp
    exact (lt_irrefl 0) hp
  apply FiniteDistribution.eq_of_weight_eq
  intro t
  rw [FiniteDistribution.weight_eq_probability_singleton,
    FiniteDistribution.weight_eq_probability_singleton]
  simp only [FiniteDistribution.probability_pushforward,
    FiniteDistribution.probability_condition]
  have hevent :
      (fun x : A × B => (slice (g x.1) && visible x.2) && decide (g x.1 = t)) =
      (fun x : A × B => (slice (g x.1) && decide (g x.1 = t)) && visible x.2) := by
    funext x
    cases hs : slice (g x.1) <;> cases he : visible x.2 <;>
      cases ht : decide (g x.1 = t) <;> rfl
  rw [hevent,
    probability_product_and μ ν (fun h : A => slice (g h) && decide (g h = t)) visible,
    probability_product_and μ ν (fun h : A => slice (g h)) visible]
  exact mul_div_mul_right _ _ hv

theorem probability_condition_congr (μ : FiniteDistribution A)
    (given event event' : A → Bool) (positive : 0 < μ.probability given)
    (agree : ∀ x, given x = true → event x = event' x) :
    (μ.condition given positive).probability event =
      (μ.condition given positive).probability event' := by
  rw [FiniteDistribution.probability_condition, FiniteDistribution.probability_condition]
  congr 1
  congr 1
  funext x
  by_cases hx : given x = true
  · rw [agree x hx]
  · simp [hx]

end FiniteLaws

section TensorMatch

variable {ℓ : Nat} {H : Type*} [AddCommGroup H] [Module F2 H]
  [Finite H] [FiniteDimensional F2 H]

theorem probability_condition_eq_conditionalMatch
    (W : Submodule F2 (Fin ℓ → F2)) (μ : FiniteDistribution (W ⊗[F2] H))
    (G : (W ⊗[F2] H) → (Fin ℓ → F2))
    (Q : Submodule F2 (Module.Dual F2 H)) (target : Q →ₗ[F2] W)
    (z : Module.Dual F2 H) (offset : Fin ℓ → F2)
    (positive : 0 < μ.probability (tensorSlice W Q target)) :
    (μ.condition (tensorSlice W Q target) positive).probability
        (fun X => decide (G X = offset + TensorBucketEvaluation.tensorOutputLinear W z X)) =
      TensorAffineHeavyWitness.conditionalMatch W μ G Q target z offset := by
  rw [FiniteDistribution.probability_condition]
  unfold TensorAffineHeavyWitness.conditionalMatch AffineLinearHeavyWitness.conditionalMatch
  congr 1
  · unfold FiniteDistribution.probability FiniteDistribution.expectation
    apply Finset.sum_congr rfl
    intro X _
    by_cases hslice : TensorRestriction.restrictionMap Q X = target <;>
      by_cases hmatch : G X = offset + TensorBucketEvaluation.tensorOutputLinear W z X <;>
      simp [tensorSlice, hslice, hmatch]
  · simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
      tensorSlice, decide_eq_true_eq, mul_ite, mul_one, mul_zero]

end TensorMatch

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper))

theorem conditional_referenceLaw (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (jointEvent slots rows upper lower W repeats cut visible Q target)) :
    ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
      (jointEvent slots rows upper lower W repeats cut visible Q target) positive).pushforward
        (hiddenOutput slots rows upper lower W repeats cut) =
      (referenceLaw slots rows upper lower W repeats cut).condition (tensorSlice W Q target)
        (slice_probability_pos slots rows upper lower W repeats cut externalLaw
          visible Q target positive) := by
  exact condition_product_hidden
    (HiddenBucketBias.hiddenTapeLaw W
      (RecursiveSampler.tapeLaw F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (visibleLaw slots rows upper lower W repeats cut externalLaw)
    (HiddenBucketBias.hiddenSum W
      (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))))
    (tensorSlice W Q target) visible positive

theorem conditional_observed_response_probability
    (a : LowerVector rows lower) (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (jointEvent slots rows upper lower W repeats cut visible Q target))
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (observed : Input slots rows upper lower W a)
    (z : Module.Dual F2 (UpperSpace slots upper)) (offset : UpperVector rows upper) :
    ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
      (jointEvent slots rows upper lower W repeats cut visible Q target) positive).probability
      (fun x => decide (response slots rows upper lower W a labeling observed
          (hiddenOutput slots rows upper lower W repeats cut x) =
        offset + TensorBucketEvaluation.tensorOutputLinear W z
          (hiddenOutput slots rows upper lower W repeats cut x))) =
      TensorAffineHeavyWitness.conditionalMatch W
        (referenceLaw slots rows upper lower W repeats cut)
        (response slots rows upper lower W a labeling observed) Q target z offset := by
  have h := congrArg (fun μ : FiniteDistribution (W ⊗[F2] UpperSpace slots upper) =>
    μ.probability (fun X => decide (response slots rows upper lower W a labeling observed X =
      offset + TensorBucketEvaluation.tensorOutputLinear W z X)))
    (conditional_referenceLaw slots rows upper lower W repeats cut externalLaw
      visible Q target positive)
  rw [FiniteDistribution.probability_pushforward] at h
  exact h.trans (probability_condition_eq_conditionalMatch W
    (referenceLaw slots rows upper lower W repeats cut)
    (response slots rows upper lower W a labeling observed) Q target z offset
    (slice_probability_pos slots rows upper lower W repeats cut externalLaw visible Q target positive))

theorem conditional_response_probability
    (a : LowerVector rows lower) (repeats : Nat → Nat) (cut : Cut upper lower)
    (externalLaw : FiniteDistribution (Exterior slots rows upper lower))
    (visible : VisibleSample slots rows upper lower W repeats cut → Bool)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper))) (target : Q →ₗ[F2] W)
    (positive : 0 < (rawLaw slots rows upper lower W repeats cut externalLaw).probability
      (jointEvent slots rows upper lower W repeats cut visible Q target))
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (observed : Input slots rows upper lower W a)
    (fixes_input : ∀ data, visible data = true →
      readInput slots rows upper lower W a
        (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper)))
        data = observed)
    (z : Module.Dual F2 (UpperSpace slots upper)) (offset : UpperVector rows upper) :
    ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
      (jointEvent slots rows upper lower W repeats cut visible Q target) positive).probability
      (fun x => decide (response slots rows upper lower W a labeling
          (readInput slots rows upper lower W a
            (RecursiveSampler.evaluate F2 repeats cut.path (LeafDomain (nodeSlots slots upper))) x.2)
          (hiddenOutput slots rows upper lower W repeats cut x) =
        offset + TensorBucketEvaluation.tensorOutputLinear W z
          (hiddenOutput slots rows upper lower W repeats cut x))) =
      TensorAffineHeavyWitness.conditionalMatch W
        (referenceLaw slots rows upper lower W repeats cut)
        (response slots rows upper lower W a labeling observed) Q target z offset := by
  trans ((rawLaw slots rows upper lower W repeats cut externalLaw).condition
    (jointEvent slots rows upper lower W repeats cut visible Q target) positive).probability
      (fun x => decide (response slots rows upper lower W a labeling observed
          (hiddenOutput slots rows upper lower W repeats cut x) =
        offset + TensorBucketEvaluation.tensorOutputLinear W z
          (hiddenOutput slots rows upper lower W repeats cut x)))
  · apply probability_condition_congr
    intro x hx
    have hv : visible x.2 = true := (Bool.and_eq_true_iff.mp hx).2
    rw [fixes_input x.2 hv]
  · exact conditional_observed_response_probability slots rows upper lower W a repeats cut
      externalLaw visible Q target positive labeling observed z offset

end
end PerfectCompleteness.OwnInputAffineSlice


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedRawPrediction

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (rows : Nat → Nat) (upper lower : Nodes branch n) (lowerLevel : Nat)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rowSpaceFintype
local instance valueFintype_r25b577_1 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
theorem conditional_prediction_eq_oai (a : Block rows lower)
    (externalLaw : FiniteDistribution (OwnInputReference.Exterior projectedSlots rows upper lower))
    (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v)
    (hne : ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v T = true)
    (positive : 0 <
      (OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).probability
        (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)) :
    ((OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).condition
      (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)
      positive).probability
        (rawPrediction originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut a) =
      RightDecoderWitness.conditionalMatch projectedSlots rows upper lower (LinearMap.ker A) a repeats cut σ
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) v)
        (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood hne)
        (nativeCorrection originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood)
        (visibleOffset originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
          A repeats cut v hgood) := by
  let μ := OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw
  let joint := OwnInputAffineSlice.jointEvent projectedSlots rows upper lower (LinearMap.ker A) repeats cut
    (fun data => decide (data = v))
    (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v hgood)
    (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v hgood hne)
  have hgiven : given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v = joint :=
    given_eq_jointEvent originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v hgood hne
  have hpositive : 0 < μ.probability joint := by
    rw [← hgiven]
    exact positive
  trans (μ.condition
    (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)
    positive).probability
      (responseMatch originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a v hgood)
  · apply OwnInputAffineSlice.probability_condition_congr
    intro sample hs
    have hp := Bool.and_eq_true_iff.mp hs
    have hv : sample.2 = v := @of_decide_eq_true _ _ hp.2
    rw [rawPrediction_eq originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut a v hgood sample hv, hp.1, Bool.true_and]
  trans (μ.condition joint hpositive).probability
    (responseMatch originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut a v hgood)
  · simp only [FiniteDistribution.probability_condition, hgiven]
  · exact OwnInputAffineSlice.conditional_response_probability projectedSlots rows upper lower (LinearMap.ker A)
      a repeats cut externalLaw (fun data => decide (data = v))
      (columnSpace originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)
      (target originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood hne) hpositive σ
      (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
        (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) v)
      (by
        intro data hdata
        have hv : data = v := @of_decide_eq_true _ _ hdata
        subst data
        rfl)
      (nativeCorrection originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)
      (visibleOffset originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v hgood)

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq_oai.{u_1} := @OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.conditional_prediction_eq_oai.{u_1}
