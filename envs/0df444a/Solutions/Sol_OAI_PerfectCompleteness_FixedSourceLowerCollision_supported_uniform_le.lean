-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedSourceLowerCollision.supported_uniform_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:22:19.924625+00:00
-- url     : https://prove2.me/submissions/88ca95c1-b35d-4087-a575-3ecc855f4800

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
import Theorems.Thm_OAI_PerfectCompleteness_FixedLowerUniformCollision_supported_collision_lt
import Theorems.Thm_OAI_PerfectCompleteness_LowerCutPairBackground_arraysPair_law

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

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeArrayInteriorExteriorLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
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

end
end PerfectCompleteness.SelectedArrayReplacement

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutNodeCoordinates
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_LowerCutNodeMatrix
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutNodeMatrix

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit WholeArrayInteriorExterior LowerCutNodeCoordinates
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem rows_transport (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
    (X : NativeMatrix rows p slots) →
      EvaluationMatrix.rows (H (nodeSlots slots (upperNode p))) (matrixEquiv rows p slots X) =
        rowEquiv rows p slots (EvaluationMatrix.rows (H (subtreeSlots p slots)) X)
  | _, _, .refl _, _, _ => rfl
  | _, _, .step i p, slots, X => rows_transport rows p (childSlots slots i) X

theorem shift_transport (rows : Nat → Nat) : {n m : Nat} →
    (p : Path branch n (m + 1)) →
    (slots : Slots branch n → Fin t → MixedSupport.Slot) →
    (X : NativeMatrix rows p slots) →
    (a : BucketSampler.Direction (rows (m + 1))) →
    (h : H (subtreeSlots p slots)) →
      matrixEquiv rows p slots (EvaluationMatrix.shift (H (subtreeSlots p slots)) X a.val h) =
        EvaluationMatrix.shift (H (nodeSlots slots (upperNode p))) (matrixEquiv rows p slots X)
          (directionEquiv rows p a).val (scalarEquiv p slots h)
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .step i p, slots, X, a, h =>
      shift_transport rows p (childSlots slots i) X a h

end
end PerfectCompleteness.LowerCutNodeMatrix

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_MultiplicationFormInjectiveLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.MultiplicationFormInjective

noncomputable section

open scoped Classical
open PointwiseSpaces OddListExtraction
open UniqueGamesTheorem.Foundations.Games

variable {X : Type*} (H : Submodule F2 (X → F2))

theorem multiplicationForm_injective :
    Function.Injective (multiplicationForm H) := by
  intro z z' h
  apply (Submodule.linearMap_eq_iff_of_eq_span z z'
    (show squareSpace H =
      Submodule.span F2 {u | ∃ f ∈ H, ∃ g ∈ H, f * g = u} from rfl)).2
  rintro ⟨u, f, hf, g, hg, rfl⟩
  exact congrArg (fun F : H →ₗ[F2] H →ₗ[F2] F2 => F ⟨f, hf⟩ ⟨g, hg⟩) h

@[simp] theorem multiplicationForm_eq_iff
    (z z' : Module.Dual F2 (squareSpace H)) :
    multiplicationForm H z = multiplicationForm H z' ↔ z = z' :=
  (multiplicationForm_injective H).eq_iff

theorem definedEqual_map_of_injective {A B : Type*} (f : A → B)
    (hf : Function.Injective f) (a b : Option A) :
    DecoderTableCoupling.definedEqual (a.map f) (b.map f) =
      DecoderTableCoupling.definedEqual a b := by
  cases a <;> cases b <;>
    simp [DecoderTableCoupling.definedEqual, hf.eq_iff]

@[simp] theorem definedEqual_map
    (a b : Option (Module.Dual F2 (squareSpace H))) :
    DecoderTableCoupling.definedEqual (a.map (multiplicationForm H))
        (b.map (multiplicationForm H)) =
      DecoderTableCoupling.definedEqual a b :=
  definedEqual_map_of_injective _ (multiplicationForm_injective H) a b

@[simp] theorem fullCollision_map
    (a b : Option (Module.Dual F2 (squareSpace H))) :
    BilinearCollisionTransfer.fullCollision (a.map (multiplicationForm H))
        (b.map (multiplicationForm H)) =
      DecoderTableCoupling.definedEqual a b :=
  definedEqual_map H a b

@[simp] theorem collision_map {Ω : Type*}
    (answers : Ω → Option (Module.Dual F2 (squareSpace H))) (p : Ω × Ω) :
    TwoResponseCollision.collision (fun x => (answers x).map (multiplicationForm H)) p =
      TwoResponseCollision.collision answers p :=
  definedEqual_map H (answers p.1) (answers p.2)

end
end PerfectCompleteness.MultiplicationFormInjective


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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_HierarchicalLowerMatrixInput
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalLowerMatrixInput

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

variable (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

theorem updateBackground_other
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (X : Matrix (rows := rows) slots upper lowerLevel d)
    (j : {j : Nodes branch n // j ≠ upper})
    (hj : j ≠ HierarchicalFrozenTables.lowerIndex upper lowerLevel d) :
    updateBackground slots upper lowerLevel background d X j = background j := by
  exact Function.update_of_ne hj _ _

end
end PerfectCompleteness.HierarchicalLowerMatrixInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_LowerCutDecoderInput
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutDecoderInput

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

theorem backgroundOf_update (arrays : Arrays slots rows)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (fresh : LowerRows (rows := rows) slots upper lowerLevel d) :
    HierarchicalMatrixTable.backgroundOf slots upper
        (Function.update arrays (HierarchicalLeftDecoder.LowerNode upper lowerLevel d) fresh) =
      HierarchicalLowerMatrixInput.updateBackground slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) d
        (EvaluationMatrix.ofRows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
          fresh) := by
  funext j
  by_cases hj : j = HierarchicalFrozenTables.lowerIndex upper lowerLevel d
  · subst j
    rw [HierarchicalLowerMatrixInput.updateBackground_selected,
      EvaluationMatrix.rows_ofRows]
    exact Function.update_self _ _ _
  · have hval : j.val ≠ HierarchicalLeftDecoder.LowerNode upper lowerLevel d := by
      intro h
      exact hj (Subtype.ext h)
    rw [HierarchicalLowerMatrixInput.updateBackground_other slots upper lowerLevel
      (HierarchicalMatrixTable.backgroundOf slots upper arrays) d _ j hj]
    exact Function.update_of_ne hval _ _

theorem upperMatrix_update (arrays : Arrays slots rows)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (fresh : LowerRows (rows := rows) slots upper lowerLevel d) :
    NodeEmbedding.matrix
        (Function.update arrays (HierarchicalLeftDecoder.LowerNode upper lowerLevel d) fresh)
        upper =
      NodeEmbedding.matrix arrays upper := by
  have hne : upper ≠ HierarchicalLeftDecoder.LowerNode upper lowerLevel d :=
    (HierarchicalFrozenTables.lowerIndex upper lowerLevel d).property.symm
  unfold NodeEmbedding.matrix NodeEmbedding.embeddedRows
  rw [Function.update_of_ne hne]

theorem actualInput_update {r : Nat} (arrays : Arrays slots rows)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (fresh : LowerRows (rows := rows) slots upper lowerLevel d) :
    actualInput slots upper lowerLevel
        (Function.update arrays (HierarchicalLeftDecoder.LowerNode upper lowerLevel d) fresh) A =
      HierarchicalLowerMatrixInput.input slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper arrays) d
        (NodeEmbedding.matrix arrays upper) A
        (EvaluationMatrix.ofRows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
          fresh) := by
  unfold actualInput
  rw [upperMatrix_update slots upper lowerLevel arrays d fresh]
  exact congrArg
    (fun background : HierarchicalMatrixTable.Background (rows := rows) slots upper =>
      (⟨background, (A, A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (NodeEmbedding.matrix arrays upper)))⟩ :
          HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r))
    (backgroundOf_update slots upper lowerLevel arrays d fresh)

end
end PerfectCompleteness.LowerCutDecoderInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutDecoderForm

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping

variable {branch rows repeats : Nat → Nat} {n height t : Nat}
  (path : Path branch n (height + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

theorem form_injective :
    Function.Injective (form path slots upper lowerLevel d hnode) := by
  intro answer answer' hform
  apply MultiplicationFormInjective.multiplicationForm_injective
    (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
  ext f g
  obtain ⟨f', rfl⟩ := (spaceEquiv path slots upper lowerLevel d hnode).surjective f
  obtain ⟨g', rfl⟩ := (spaceEquiv path slots upper lowerLevel d hnode).surjective g
  exact congrArg (fun F : ChildBilinearCollisionTransfer.ParentForm
    (cutSlots path slots) => F f' g') hform

variable (hbranch : ∀ k < n, 0 < branch k) {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (table : HierarchicalAllDecoderTables.Input (rows := rows)
    slots upper lowerLevel adviceRows → HierarchicalAllDecoderTables.UpperAnswer slots upper)
  (cutoff : Nat)

theorem fullCollision_readForm (arrays arrays' : Arrays slots rows) :
    BilinearCollisionTransfer.fullCollision
        (readForm path slots upper lowerLevel d hnode hbranch A table cutoff arrays)
        (readForm path slots upper lowerLevel d hnode hbranch A table cutoff arrays') =
      DecoderTableCoupling.definedEqual
        (answer slots upper lowerLevel d hbranch A table cutoff arrays)
        (answer slots upper lowerLevel d hbranch A table cutoff arrays') :=
  MultiplicationFormInjective.definedEqual_map_of_injective
    (form path slots upper lowerLevel d hnode)
    (form_injective path slots upper lowerLevel d hnode) _ _

theorem fullCollision_pair (exterior : Exterior rows repeats path slots)
    (direction : BucketSampler.Direction (rows (height + 1)))
    (raw : LowerCutPair.Raw rows repeats path slots) :
    BilinearCollisionTransfer.fullCollision
        (first path slots upper lowerLevel d hnode hbranch A table cutoff exterior raw)
        (second path slots upper lowerLevel d hnode hbranch A table cutoff exterior direction raw) =
      TwoResponseCollision.collision
        (answer slots upper lowerLevel d hbranch A table cutoff)
        (LowerCutPair.arraysPair rows repeats path slots exterior direction raw) :=
  fullCollision_readForm path slots upper lowerLevel d hnode hbranch A table cutoff _ _

end
end PerfectCompleteness.LowerCutDecoderForm

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutScalarProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionLowerForms

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

section Casts

variable {branch : Nat → Nat} {height t : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat)
  {source target : Slots branch (height + 1) → Fin t → MixedSupport.Slot}

theorem rawCast_law (h : source = target) :
    (CutChildGrouping.rawLaw (C := C) source rows).pushforward (rawCast rows h) =
      CutChildGrouping.rawLaw (C := C) target rows := by
  cases h
  exact FiniteDistribution.pushforward_id _

theorem formCast_injective (h : source = target) :
    Function.Injective (CutNativeForms.formCast h) := by
  cases h
  exact Function.injective_id

theorem fullCollision_formCast (h : source = target)
    (F G : Option (ChildBilinearCollisionTransfer.ParentForm source)) :
    BilinearCollisionTransfer.fullCollision (F.map (CutNativeForms.formCast h))
        (G.map (CutNativeForms.formCast h)) =
      BilinearCollisionTransfer.fullCollision F G :=
  MultiplicationFormInjective.definedEqual_map_of_injective
    (CutNativeForms.formCast h) (formCast_injective h) F G

end Casts

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)

theorem rawAtCut_law
    (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :
    (CutChildGrouping.rawLaw (C := Calls (rows := rows) (repeats := repeats) path)
      (SourceChildMarkedLaw.questionSlots clauses q) rows).pushforward
        (rawAtCut (rows := rows) (repeats := repeats) path outside clauses q) =
      CutChildGrouping.rawLaw (C := Calls (rows := rows) (repeats := repeats) path)
        (WholeCutGrouping.cutSlots path (slots path outside clauses q)) rows :=
  rawCast_law rows (cutSlots_eq path outside clauses q).symm

variable (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)

variable (tables : (q : Questions (branch := branch) (height := height) (t := t) (m := m)) →
  UpperTable (rows := rows) path outside clauses upper level (adviceRows := adviceRows) q)
  (cutoff : Nat)

theorem fullCollision_probability
    (direction : BucketSampler.Direction (rows (height + 1)))
    (q : Questions (branch := branch) (height := height) (t := t) (m := m)) :
    (CutChildGrouping.rawLaw (C := Calls (rows := rows) (repeats := repeats) path)
      (SourceChildMarkedLaw.questionSlots clauses q) rows).probability
        (fun raw => BilinearCollisionTransfer.fullCollision
          (first path outside placeholder clauses upper level d hnode hbranch A exterior tables cutoff q raw)
          (second path outside placeholder clauses upper level d hnode hbranch A exterior tables cutoff
            direction q raw)) =
      (CutChildGrouping.rawLaw (C := Calls (rows := rows) (repeats := repeats) path)
        (WholeCutGrouping.cutSlots path (slots path outside clauses q)) rows).probability
        (fun raw => BilinearCollisionTransfer.fullCollision
          (LowerCutDecoderForm.first path (slots path outside clauses q) upper level d hnode hbranch A
            (tables q) cutoff (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
              (SourceChildMarkedLaw.questionSlots clauses q) exterior) raw)
          (LowerCutDecoderForm.second path (slots path outside clauses q) upper level d hnode hbranch A
            (tables q) cutoff (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
              (SourceChildMarkedLaw.questionSlots clauses q) exterior) direction raw)) := by
  have h := congrArg (fun μ : FiniteDistribution
      (CutChildGrouping.Raw (C := Calls (rows := rows) (repeats := repeats) path)
        (WholeCutGrouping.cutSlots path (slots path outside clauses q)) rows) => μ.probability
    (fun raw => BilinearCollisionTransfer.fullCollision
      (LowerCutDecoderForm.first path (slots path outside clauses q) upper level d hnode hbranch A
        (tables q) cutoff (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
          (SourceChildMarkedLaw.questionSlots clauses q) exterior) raw)
      (LowerCutDecoderForm.second path (slots path outside clauses q) upper level d hnode hbranch A
        (tables q) cutoff (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
          (SourceChildMarkedLaw.questionSlots clauses q) exterior) direction raw)))
    (rawAtCut_law (rows := rows) (repeats := repeats) path outside clauses q)
  rw [FiniteDistribution.probability_pushforward] at h
  simpa only [first, second, fullCollision_formCast] using h

end
end PerfectCompleteness.SourceQuestionLowerForms

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairBackground
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

theorem installMatrix_eq_update (exterior : Exterior rows repeats p slots)
    (c : Complement rows repeats p slots) (X : NativeMatrix rows p slots) :
    installMatrix rows repeats p slots exterior c X =
      Function.update (backgroundArrays rows repeats p slots exterior c)
        (WholeArrayInteriorExterior.upperNode p)
        (LowerCutNodeCoordinates.rowEquiv rows p slots
          (EvaluationMatrix.rows (H (cutSlots p slots)) X)) :=
  LowerCutNodeCoordinates.replace_eq_update rows p slots _ _

end
end PerfectCompleteness.LowerCutPairBackground

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_LowerCutInstalledInput
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutInstalledInput

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

section NodeEquality

variable (rows : Nat → Nat) (slots : Slots branch n → Fin t → MixedSupport.Slot)

theorem rows_matrixCast {i j : Nodes branch n} (h : i = j)
    (X : NodeMatrix rows slots i) :
    EvaluationMatrix.rows (H (nodeSlots slots j)) (matrixCast rows slots h X) =
      rowCast rows slots h (EvaluationMatrix.rows (H (nodeSlots slots i)) X) := by
  subst j
  rfl

theorem shift_matrixCast {i j : Nodes branch n} (h : i = j)
    (X : NodeMatrix rows slots i) (a : BucketSampler.Direction (rows (Nodes.height i)))
    (v : H (nodeSlots slots i)) :
    matrixCast rows slots h (EvaluationMatrix.shift (H (nodeSlots slots i)) X a.val v) =
      EvaluationMatrix.shift (H (nodeSlots slots j)) (matrixCast rows slots h X)
        (directionCast rows h a).val (scalarCast slots h v) := by
  subst j
  rfl

theorem update_rowCast {i j : Nodes branch n} (h : i = j)
    (arrays : Arrays slots rows) (S : NodeRows rows slots i) :
    Function.update arrays i S = Function.update arrays j (rowCast rows slots h S) := by
  subst j
  rfl

end NodeEquality

variable (rows : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

theorem rows_lowerMatrixEquiv (X : LowerCutPair.NativeMatrix rows p slots) :
    EvaluationMatrix.rows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (lowerMatrixEquiv rows p slots upper lowerLevel d hnode X) =
      rowCast rows slots hnode
        (LowerCutNodeCoordinates.rowEquiv rows p slots
          (EvaluationMatrix.rows (H (WholeCutGrouping.cutSlots p slots)) X)) := by
  change EvaluationMatrix.rows (H (nodeSlots slots (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))
    (matrixCast rows slots hnode (LowerCutNodeMatrix.matrixEquiv rows p slots X)) = _
  rw [rows_matrixCast, LowerCutNodeMatrix.rows_transport]

theorem shift_lowerMatrixEquiv (X : LowerCutPair.NativeMatrix rows p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (v : H (WholeCutGrouping.cutSlots p slots)) :
    lowerMatrixEquiv rows p slots upper lowerLevel d hnode
        (EvaluationMatrix.shift (H (WholeCutGrouping.cutSlots p slots)) X a.val v) =
      EvaluationMatrix.shift (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (lowerMatrixEquiv rows p slots upper lowerLevel d hnode X)
        (lowerDirectionEquiv rows p upper lowerLevel d hnode a).val
        (lowerScalarEquiv p slots upper lowerLevel d hnode v) := by
  change matrixCast rows slots hnode
    (LowerCutNodeMatrix.matrixEquiv rows p slots
      (EvaluationMatrix.shift (H (WholeCutGrouping.cutSlots p slots)) X a.val v)) = _
  rw [LowerCutNodeMatrix.shift_transport]
  exact shift_matrixCast rows slots hnode (LowerCutNodeMatrix.matrixEquiv rows p slots X)
    (LowerCutNodeCoordinates.directionEquiv rows p a)
    (LowerCutNodeCoordinates.scalarEquiv p slots v)

variable (repeats : Nat → Nat)

local instance nativeMatrixFintype_r4c2e38_1 : Fintype (LowerCutPair.NativeMatrix rows p slots) :=
  Fintype.ofEquiv (LowerCutPair.NativeRows rows p slots)
    (EvaluationMatrix.rowsEquiv (H (WholeCutGrouping.cutSlots p slots))).symm
local instance lowerMatrixFintype_r4c2e38_1 : Fintype
    (HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d) :=
  Fintype.ofEquiv
    (Fin (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) →
      HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
    (EvaluationMatrix.rowsEquiv (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)).symm
theorem actualInput_installMatrix {r : Nat}
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (c : LowerCutPairBackground.Complement rows repeats p slots)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (X : LowerCutPair.NativeMatrix rows p slots) :
    LowerCutDecoderInput.actualInput slots upper lowerLevel
        (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X) A =
      HierarchicalLowerMatrixInput.input slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper
          (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c)) d
        (NodeEmbedding.matrix (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) upper)
        A (lowerMatrixEquiv rows p slots upper lowerLevel d hnode X) := by
  rw [LowerCutPairBackground.installMatrix_eq_update, update_rowCast rows slots hnode]
  have h := LowerCutDecoderInput.actualInput_update slots upper lowerLevel
    (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) d A
    (rowCast rows slots hnode (LowerCutNodeCoordinates.rowEquiv rows p slots
      (EvaluationMatrix.rows (H (WholeCutGrouping.cutSlots p slots)) X)))
  have hX : EvaluationMatrix.ofRows (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
      (rowCast rows slots hnode (LowerCutNodeCoordinates.rowEquiv rows p slots
        (EvaluationMatrix.rows (H (WholeCutGrouping.cutSlots p slots)) X))) =
      lowerMatrixEquiv rows p slots upper lowerLevel d hnode X := by
    rw [← rows_lowerMatrixEquiv rows p slots upper lowerLevel d hnode,
      EvaluationMatrix.ofRows_rows]
  rw [hX] at h
  exact h

end
end PerfectCompleteness.LowerCutInstalledInput

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_PreliminaryAveraging
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PreliminaryAveraging

open PreliminarySampler TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

theorem probability_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteDistribution X) (ν : FiniteDistribution Y) (event : X × Y → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun x => ν.probability (fun y => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

end
end PerfectCompleteness.PreliminaryAveraging

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutUniformCoordinatesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutUniformCoordinates

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}
  (rows : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)

variable [Nonempty (BucketSampler.Direction (rows (m + 1)))]

attribute [local instance] OAI.PerfectCompleteness.LowerCutUniformCoordinates.lowerHFintype
theorem uniformLaw_pushforward :
    letI := lowerDirection_nonempty rows p upper lowerLevel d hnode
    (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))).pushforward (sampleEquiv rows p slots upper lowerLevel d hnode) =
      FixedLowerUniformCollision.uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) := by
  let := lowerDirection_nonempty rows p upper lowerLevel d hnode
  have h := UniformConditioning.uniform_transport (sampleEquiv rows p slots upper lowerLevel d hnode)
  rw [FiniteDistribution.transport_eq_pushforward] at h
  simpa only [FixedLowerUniformCollision.uniformLaw, WholeCutSampler.uniform_product] using h

theorem probability_transport (event : LowerSample rows slots upper lowerLevel d → Bool) :
    letI := lowerDirection_nonempty rows p upper lowerLevel d hnode
    (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))).probability
        (fun x => event (sampleEquiv rows p slots upper lowerLevel d hnode x)) =
      (FixedLowerUniformCollision.uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).probability event := by
  let := lowerDirection_nonempty rows p upper lowerLevel d hnode
  have h := congrArg
    (fun μ : FiniteDistribution (LowerSample rows slots upper lowerLevel d) => μ.probability event)
    (uniformLaw_pushforward rows p slots upper lowerLevel d hnode)
  rw [FiniteDistribution.probability_pushforward] at h
  exact h

variable {Y : Type*} [Fintype Y]

omit [Nonempty (BucketSampler.Direction (rows (m + 1)))] [Fintype Y] in
theorem collision_transport
    (f : HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d → Option Y)
    (x : NativeSample rows p slots) :
    FixedLowerUniformCollision.uniformCollision (H (WholeCutGrouping.cutSlots p slots))
        (rows (m + 1))
        (fun X => f (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode X)) x =
      FixedLowerUniformCollision.uniformCollision
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) f
        (sampleEquiv rows p slots upper lowerLevel d hnode x) := by
  exact congrArg
    (fun X => TwoResponseCollision.collision f
      (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode x.2.1, X))
    (LowerCutInstalledInput.shift_lowerMatrixEquiv rows p slots upper lowerLevel d hnode
      x.2.1 x.1 x.2.2)

omit [Fintype Y] in
theorem collision_probability
    (f : HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d → Option Y) :
    letI := lowerDirection_nonempty rows p upper lowerLevel d hnode
    (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))).probability
        (FixedLowerUniformCollision.uniformCollision (H (WholeCutGrouping.cutSlots p slots))
          (rows (m + 1))
          (fun X => f (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode X))) =
      (FixedLowerUniformCollision.uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).probability
          (FixedLowerUniformCollision.uniformCollision
            (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
            (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))) f) := by
  let := lowerDirection_nonempty rows p upper lowerLevel d hnode
  have hevent := funext (collision_transport rows p slots upper lowerLevel d hnode f)
  rw [hevent]
  exact probability_transport rows p slots upper lowerLevel d hnode _

end
end PerfectCompleteness.LowerCutUniformCoordinates

end

section

namespace PerfectCompleteness.LowerCutUniformCollisionLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

theorem direction_probability_eq {Y : Type*} [Fintype Y]
    (answer : Arrays slots rows → Option Y)
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) :
    (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
      (WholeCutGrouping.cutSlots p slots) rows).probability
        (fun raw => TwoResponseCollision.collision answer
          (LowerCutPair.arraysPair rows repeats p slots exterior a raw)) =
      (FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats p slots)).expectation
        (fun c => ((FiniteDistribution.uniform (LowerCutPair.NativeMatrix rows p slots)).product
          (FiniteDistribution.uniform (H (WholeCutGrouping.cutSlots p slots)))).probability
            (fun z => TwoResponseCollision.collision
              (fun X => answer (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X))
              (z.1, EvaluationMatrix.shift (H (WholeCutGrouping.cutSlots p slots)) z.1 a.val z.2))) := by
  have h := congrArg
    (fun μ : FiniteDistribution (Arrays slots rows × Arrays slots rows) =>
      μ.probability (TwoResponseCollision.collision answer))
    (LowerCutPairBackground.arraysPair_law rows repeats p slots exterior a)
  simp only [FiniteDistribution.probability_pushforward] at h
  rw [PreliminaryAveraging.probability_product] at h
  simp only [FiniteDistribution.probability_pushforward] at h
  exact h

theorem native_probability_eq {Y : Type*} [Fintype Y]
    [Nonempty (BucketSampler.Direction (rows (m + 1)))]
    (answer : Arrays slots rows → Option Y)
    (exterior : WholeCutGrouping.Exterior rows repeats p slots) :
    (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).expectation
      (fun a => (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
        (WholeCutGrouping.cutSlots p slots) rows).probability
          (fun raw => TwoResponseCollision.collision answer
            (LowerCutPair.arraysPair rows repeats p slots exterior a raw))) =
      (FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats p slots)).expectation
        (fun c => (FixedLowerUniformCollision.uniformLaw (H (WholeCutGrouping.cutSlots p slots))
          (rows (m + 1))).probability
            (FixedLowerUniformCollision.uniformCollision _ _
              (fun X => answer (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X)))) := by
  simp_rw [direction_probability_eq rows repeats p slots answer exterior]
  rw [FiniteDistribution.expectation_comm]
  apply FiniteDistribution.expectation_congr
  intro c
  exact (PreliminaryAveraging.probability_product
    (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1))))
    ((FiniteDistribution.uniform (LowerCutPair.NativeMatrix rows p slots)).product
      (FiniteDistribution.uniform (H (WholeCutGrouping.cutSlots p slots))))
    (FixedLowerUniformCollision.uniformCollision (H (WholeCutGrouping.cutSlots p slots))
      (rows (m + 1))
      (fun X => answer (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X)))).symm

variable (upper : Nodes branch n) (lowerLevel : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
  (hnode : WholeArrayInteriorExterior.upperNode p =
    HierarchicalLeftDecoder.LowerNode upper lowerLevel d)
  (hbranch : ∀ k < n, 0 < branch k) {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (table : HierarchicalAllDecoderTables.Input (rows := rows)
    slots upper lowerLevel adviceRows → HierarchicalAllDecoderTables.UpperAnswer slots upper)
  (cutoff : Nat)

attribute [local instance] OAI.PerfectCompleteness.LowerCutUniformCollisionLaw.lowerHFintype
attribute [local instance] OAI.PerfectCompleteness.LowerCutUniformCollisionLaw.answerFintype
theorem answer_installMatrix
    (exterior : WholeCutGrouping.Exterior rows repeats p slots)
    (c : LowerCutPairBackground.Complement rows repeats p slots)
    (X : LowerCutPair.NativeMatrix rows p slots) :
    LowerCutDecoderForm.answer slots upper lowerLevel d hbranch A table cutoff
        (LowerCutPairBackground.installMatrix rows repeats p slots exterior c X) =
      HierarchicalLowerInverse.matrixTable slots upper lowerLevel
        (HierarchicalMatrixTable.backgroundOf slots upper
          (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c)) d
        (NodeEmbedding.matrix (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) upper)
        A (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d cutoff table)
        (LowerCutInstalledInput.lowerMatrixEquiv rows p slots upper lowerLevel d hnode X) := by
  exact congrArg
    (fun input : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel adviceRows =>
      HierarchicalDecoderTables.decode slots upper lowerLevel hbranch d cutoff (table input))
    (LowerCutInstalledInput.actualInput_installMatrix rows p slots upper lowerLevel d hnode
      repeats exterior c A X)

include hnode in

theorem probability_eq
    [Nonempty (BucketSampler.Direction (rows (m + 1)))]
    [Nonempty (BucketSampler.Direction
      (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d))))]
    (exterior : WholeCutGrouping.Exterior rows repeats p slots) :
    (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).expectation
      (fun a => (CutChildGrouping.rawLaw (C := Option (LowerCutPair.Calls rows repeats p))
        (WholeCutGrouping.cutSlots p slots) rows).probability
          (fun raw => TwoResponseCollision.collision
            (LowerCutDecoderForm.answer slots upper lowerLevel d hbranch A table cutoff)
            (LowerCutPair.arraysPair rows repeats p slots exterior a raw))) =
      (FiniteDistribution.uniform (LowerCutPairBackground.Complement rows repeats p slots)).expectation
        (fun c => (FixedLowerUniformCollision.uniformLaw
          (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
          (rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).probability
            (FixedLowerUniformCollision.uniformCollision _ _
              (HierarchicalLowerInverse.matrixTable slots upper lowerLevel
                (HierarchicalMatrixTable.backgroundOf slots upper
                  (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c)) d
                (NodeEmbedding.matrix
                  (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) upper)
                A (HierarchicalAllDecoderTables.decodeTable
                  slots upper lowerLevel hbranch adviceRows d cutoff table)))) := by
  rw [native_probability_eq rows repeats p slots]
  apply FiniteDistribution.expectation_congr
  intro c
  have h := LowerCutUniformCoordinates.collision_probability rows p slots upper lowerLevel d hnode
    (HierarchicalLowerInverse.matrixTable slots upper lowerLevel
      (HierarchicalMatrixTable.backgroundOf slots upper
        (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c)) d
      (NodeEmbedding.matrix (LowerCutPairBackground.backgroundArrays rows repeats p slots exterior c) upper)
      A (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d cutoff table))
  have hf := funext
    (answer_installMatrix rows repeats p slots upper lowerLevel d hnode hbranch A table cutoff exterior c)
  rw [hf]
  exact h

end
end PerfectCompleteness.LowerCutUniformCollisionLaw

end

section

namespace PerfectCompleteness.FixedLowerRawCollision

noncomputable section

open scoped Classical
open FixedParameters FixedRows RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {δ : ℚ} {hδ : 0 < δ} (parameters : Parameters δ hδ)
  {height t : Nat}
  (path : Path (branch parameters) parameters.plan.depth (height + 1))
  (slots : Slots (branch parameters) parameters.plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes (branch parameters) parameters.plan.depth)
  (d : HierarchicalFrozenTables.LowerNodes upper (height + 1))
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper (height + 1) d)

attribute [local instance] OAI.PerfectCompleteness.FixedLowerRawCollision.cutDirectionNonempty
local instance lowerDirectionNonempty :
    Nonempty (BucketSampler.Direction (rows parameters.plan
      (Nodes.height (HierarchicalLeftDecoder.LowerNode upper (height + 1) d)))) :=
  ⟨BucketUniform.coordinateDirection ⟨0, lt_of_lt_of_le Nat.zero_lt_one
    (parameters.plan.rows_pos (parameters.plan.depth -
      Nodes.height (HierarchicalLeftDecoder.LowerNode upper (height + 1) d)))⟩⟩

variable {adviceRows : Nat}
  (A : ManyGoodRows.RowMap (Block (rows parameters.plan) upper) adviceRows)
  (exterior : WholeCutGrouping.Exterior (rows parameters.plan) (repeats parameters.plan) path slots)

variable
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount (branch parameters) parameters.plan.depth t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows parameters.plan) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper (height + 1) bg → Prop)
  (density : ℝ) (hdensity : 0 < density)

include σ useful density hdensity

local instance lowerHFintype_r4c2e38_1 :
    Fintype (HierarchicalDecoderTables.LowerH slots upper (height + 1) d) :=
  Fintype.ofFinite _
local instance upperDualFintype_r4c2e38_1 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper
theorem supported_fullCollision_le
    (table : UpperTable parameters slots upper (height := height) (adviceRows := adviceRows))
    (hsupport : (HierarchicalAllDecoderTables.upperTableLaw slots upper (height + 1)
      σ useful adviceRows density).weight table ≠ 0) :
    fullCollisionProbability parameters path slots upper d hnode A exterior table ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 := by
  unfold fullCollisionProbability
  simp_rw [LowerCutDecoderForm.fullCollision_pair]
  rw [LowerCutUniformCollisionLaw.probability_eq
    (rows parameters.plan) (repeats parameters.plan) path slots upper (height + 1) d hnode
    (branchPositive parameters) A table (cutoff parameters.plan hδ) exterior]
  apply (SmallBias.expectation_mono _ (fun c =>
    (FixedLowerUniformCollision.supported_collision_lt parameters.plan hδ slots upper (height + 1)
      (HierarchicalMatrixTable.backgroundOf slots upper
        (LowerCutPairBackground.backgroundArrays (rows parameters.plan) (repeats parameters.plan)
          path slots exterior c))
      (branchPositive parameters) σ useful density hdensity d
      (NodeEmbedding.matrix (LowerCutPairBackground.backgroundArrays
        (rows parameters.plan) (repeats parameters.plan) path slots exterior c) upper)
      A table hsupport).le)).trans
  exact le_of_eq (SmallBias.expectation_const _ _)

end
end PerfectCompleteness.FixedLowerRawCollision

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

local instance rowSpaceFintype_r4c2e38_1 (q : Questions (m := m) parameters (height := height)) :
    Fintype (NodeEmbedding.RowSpace (SourceQuestionLowerForms.slots path outside clauses q) upper) :=
  Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.FixedSourceLowerCollision.upperAnswerFintype
attribute [local instance] OAI.PerfectCompleteness.FixedSourceLowerCollision.tableFintype
attribute [local instance] OAI.PerfectCompleteness.FixedSourceLowerCollision.directionNonempty
omit [NeZero m] in
private theorem supported_row
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (hsupport : (tableLaw parameters path outside clauses upper σ useful density).weight tables ≠ 0)
    (q : Questions (m := m) parameters (height := height)) :
    (HierarchicalAllDecoderTables.upperTableLaw
      (SourceQuestionLowerForms.slots path outside clauses q) upper (height + 1)
      σ (useful q) adviceRows density).weight (tables q) ≠ 0 := by
  intro hz
  apply hsupport
  exact Finset.prod_eq_zero (Finset.mem_univ q) hz

theorem supported_uniform_le_oai (hdensity : 0 < density)
    (tables : TableFamily parameters path outside clauses upper (adviceRows := adviceRows))
    (hsupport : (tableLaw parameters path outside clauses upper σ useful density).weight tables ≠ 0) :
    (FiniteDistribution.uniform (BucketSampler.Direction (rows parameters.plan (height + 1)))).expectation
      (uniformProbability parameters path outside placeholder clauses upper d hnode A exterior tables) ≤
      FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8 := by
  have hprob :
      uniformProbability parameters path outside placeholder clauses upper d hnode A exterior tables =
        fun direction => (PreliminarySampler.questionsLaw
          (branch := branch parameters) (n := height + 1)
          (t := sourceLength parameters.plan hδ) (m := m)).expectation (fun q =>
            (CutChildGrouping.rawLaw (C := FixedSourceChildCollision.Calls parameters path)
              (SourceChildMarkedLaw.questionSlots clauses q) (rows parameters.plan)).probability
                (fun raw => BilinearCollisionTransfer.fullCollision
                  (first parameters path outside placeholder clauses upper d hnode A exterior tables q raw)
                  (second parameters path outside placeholder clauses upper d hnode A exterior tables
                    direction q raw))) := by
    funext direction
    exact CompletionSoundness.sigmaLaw_probability _ _ _
  rw [hprob, FiniteDistribution.expectation_comm]
  calc
    _ ≤ (PreliminarySampler.questionsLaw (branch := branch parameters) (n := height + 1)
        (t := sourceLength parameters.plan hδ) (m := m)).expectation
          (fun _ => FixedRankContradiction.gamma parameters (Nodes.height upper) ^ 2 / 8) := by
      apply SmallBias.expectation_mono
      intro q
      have heq :
          (FiniteDistribution.uniform (BucketSampler.Direction
            (rows parameters.plan (height + 1)))).expectation
            (fun direction => (CutChildGrouping.rawLaw
              (C := FixedSourceChildCollision.Calls parameters path)
              (SourceChildMarkedLaw.questionSlots clauses q) (rows parameters.plan)).probability
                (fun raw => BilinearCollisionTransfer.fullCollision
                  (first parameters path outside placeholder clauses upper d hnode A exterior tables q raw)
                  (second parameters path outside placeholder clauses upper d hnode A exterior tables
                    direction q raw))) =
            FixedLowerRawCollision.fullCollisionProbability parameters path
              (SourceQuestionLowerForms.slots path outside clauses q) upper d hnode A
              (CleanPhysicalReplay.exteriorAt (rows parameters.plan) (repeats parameters.plan)
                path outside placeholder (SourceChildMarkedLaw.questionSlots clauses q) exterior)
              (tables q) := by
        apply FiniteDistribution.expectation_congr
        intro direction
        exact SourceQuestionLowerForms.fullCollision_probability path outside placeholder clauses upper
          (height + 1) d hnode (FixedLowerRawCollision.branchPositive parameters) A exterior tables
          (cutoff parameters.plan hδ) direction q
      rw [heq]
      exact FixedLowerRawCollision.supported_fullCollision_le parameters path
        (SourceQuestionLowerForms.slots path outside clauses q) upper d hnode A
        (CleanPhysicalReplay.exteriorAt (rows parameters.plan) (repeats parameters.plan)
          path outside placeholder (SourceChildMarkedLaw.questionSlots clauses q) exterior)
        σ (useful q) density hdensity (tables q)
        (supported_row parameters path outside clauses upper σ useful density tables hsupport q)
    _ = _ := SmallBias.expectation_const _ _

end
end PerfectCompleteness.FixedSourceLowerCollision

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedSourceLowerCollision.supported_uniform_le_oai := @OAI.PerfectCompleteness.FixedSourceLowerCollision.supported_uniform_le_oai
