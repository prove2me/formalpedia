-- Prove2me | solution 1 for OAI.PerfectCompleteness.StoppedUsefulPairLaw.observe_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:27:09.586577+00:00
-- url     : https://prove2.me/submissions/0b646445-3899-4ab3-b181-339c34bd75fd

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
import Definitions.Def_OAIQ252P020
import Theorems.Thm_OAI_PerfectCompleteness_StoppedUsefulPairLaw_readout_law

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_CutBucketTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutBucketTransportActual

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

attribute [local instance] OAI.PerfectCompleteness.CutBucketTransportActual.rowSpaceFintype
theorem tapeLaw_pushforward (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (scalar : FiniteDistribution (H (cutSlots p slots))) :
    (BucketSampler.tapeLaw (rows (m + 1)) scalar).pushforward
        (CutNodeRows.bucketTapeEquiv rows p slots) =
      BucketSampler.tapeLaw (rows (Nodes.height (upperNode p)))
        (scalar.pushforward (CutNodeRows.cutRowEquiv p slots)) := by
  have hscalar := FiniteDistribution.transport_eq_pushforward scalar
    (CutNodeRows.cutRowEquiv p slots).toEquiv
  change scalar.transport (CutNodeRows.cutRowEquiv p slots).toEquiv =
    scalar.pushforward (CutNodeRows.cutRowEquiv p slots) at hscalar
  rw [← FiniteDistribution.transport_eq_pushforward
      (BucketSampler.tapeLaw (rows (m + 1)) scalar) (CutNodeRows.bucketTapeEquiv rows p slots),
    ← hscalar]
  apply FiniteDistribution.eq_of_weight_eq
  intro tape
  change (∏ a : BucketSampler.Direction (rows (m + 1)),
      scalar.weight ((CutNodeRows.cutRowEquiv p slots).symm
        (tape (CutNodeRows.directionEquiv rows p a)))) =
    ∏ a : BucketSampler.Direction (rows (Nodes.height (upperNode p))),
      scalar.weight ((CutNodeRows.cutRowEquiv p slots).symm (tape a))
  exact (CutNodeRows.directionEquiv rows p).prod_comp (M := ℝ)
    (fun a : BucketSampler.Direction (rows (Nodes.height (upperNode p))) =>
      scalar.weight ((CutNodeRows.cutRowEquiv p slots).symm (tape a)))

theorem bucketSampleLaw_pushforward (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (directions : FiniteDistribution (BucketSampler.Direction (rows (m + 1))))
    (scalar : FiniteDistribution (H (cutSlots p slots))) :
    (directions.product ((BucketSampler.tapeLaw (rows (m + 1)) scalar).product scalar)).pushforward
        (CutNodeRows.bucketSampleEquiv rows p slots) =
      (directions.pushforward (CutNodeRows.directionEquiv rows p)).product
        ((BucketSampler.tapeLaw (rows (Nodes.height (upperNode p)))
          (scalar.pushforward (CutNodeRows.cutRowEquiv p slots))).product
            (scalar.pushforward (CutNodeRows.cutRowEquiv p slots))) := by
  change (directions.product
      ((BucketSampler.tapeLaw (rows (m + 1)) scalar).product scalar)).pushforward
        (fun z => (CutNodeRows.directionEquiv rows p z.1,
          (CutNodeRows.bucketTapeEquiv rows p slots z.2.1,
            CutNodeRows.cutRowEquiv p slots z.2.2))) = _
  rw [FiniteDistribution.product_pushforward directions
    ((BucketSampler.tapeLaw (rows (m + 1)) scalar).product scalar)
    (CutNodeRows.directionEquiv rows p)
    (fun z => (CutNodeRows.bucketTapeEquiv rows p slots z.1,
      CutNodeRows.cutRowEquiv p slots z.2))]
  rw [FiniteDistribution.product_pushforward
    (BucketSampler.tapeLaw (rows (m + 1)) scalar) scalar
    (CutNodeRows.bucketTapeEquiv rows p slots) (CutNodeRows.cutRowEquiv p slots),
    tapeLaw_pushforward]

theorem nativeLaw_pushforward (rows : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (scalar : FiniteDistribution (H (cutSlots p slots))) (hrows : 0 < rows (m + 1)) :
    (nativeLaw rows p slots scalar hrows).pushforward (CutNodeRows.bucketSampleEquiv rows p slots) =
      HierarchicalUsefulCollision.bucketLaw slots (upperNode p)
        (scalar.pushforward (CutNodeRows.cutRowEquiv p slots))
        (by simpa only [upperNode_height] using hrows) := by
  let : Nonempty (BucketSampler.Direction (rows (m + 1))) :=
    ⟨BucketUniform.coordinateDirection ⟨0, hrows⟩⟩
  let : Nonempty (BucketSampler.Direction (rows (Nodes.height (upperNode p)))) :=
    ⟨CutNodeRows.directionEquiv rows p (BucketUniform.coordinateDirection ⟨0, hrows⟩)⟩
  have hdirections :
      (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).pushforward
          (CutNodeRows.directionEquiv rows p) =
        HierarchicalUsefulCollision.directionLaw (rows := rows) (upperNode p)
          (by simpa only [upperNode_height] using hrows) := by
    change (FiniteDistribution.uniform (BucketSampler.Direction (rows (m + 1)))).pushforward
      (CutNodeRows.directionEquiv rows p) =
        FiniteDistribution.uniform (BucketSampler.Direction (rows (Nodes.height (upperNode p))))
    rw [← FiniteDistribution.transport_eq_pushforward]
    exact UniformConditioning.uniform_transport (CutNodeRows.directionEquiv rows p)
  unfold nativeLaw HierarchicalUsefulCollision.bucketLaw
  rw [bucketSampleLaw_pushforward, hdirections]

end
end PerfectCompleteness.CutBucketTransportActual

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DependentPredictionDifferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

theorem pushforward_fiber {S : Type*} [Fintype S] {X Y : S → Type*}
    [∀ s, Fintype (X s)] [∀ s, Fintype (Y s)]
    (μ : FiniteDistribution S) (P : (s : S) → FiniteDistribution (X s))
    (f : (s : S) → X s → Y s) :
    (sigmaLaw μ P).pushforward (fun x => (⟨x.1, f x.1 x.2⟩ : Σ s, Y s)) =
      sigmaLaw μ (fun s => (P s).pushforward (f s)) := by
  apply eq_of_probability_eq
  intro event
  rw [FiniteDistribution.probability_pushforward, sigmaLaw_probability, sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro s
  rw [FiniteDistribution.probability_pushforward]

end
end PerfectCompleteness.SigmaObservation

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketDescriptorLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BucketDescriptorLaw

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {D E T V : Type*} [Fintype D] [Fintype E] [Fintype T] [Fintype V]

theorem reorder_law {B : Type*} [Fintype B]
    (δ : FiniteDistribution D) (ν : FiniteDistribution E)
    (κ : FiniteDistribution B) (ρ : FiniteDistribution V) :
    (δ.product ((ν.product κ).product ρ)).pushforward
        (fun z => (⟨z.2.1.1, (z.1, (z.2.1.2, z.2.2))⟩ : Σ _ : E, D × (B × V))) =
      CompletionSoundness.sigmaLaw ν (fun _ => δ.product (κ.product ρ)) := by
  change (δ.product ((ν.product κ).product ρ)).pushforward (reorder D E B V) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  change δ.weight z.2.1 * ((ν.weight z.1 * κ.weight z.2.2.1) * ρ.weight z.2.2.2) =
    ν.weight z.1 * (δ.weight z.2.1 * (κ.weight z.2.2.1 * ρ.weight z.2.2.2))
  rw [mul_assoc]
  exact mul_left_comm _ _ _

end
end PerfectCompleteness.BucketDescriptorLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_StoppedUsefulPairLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedUsefulPairLaw

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped Classical

noncomputable section

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {N j i t : Nat}

attribute [local instance] OAI.PerfectCompleteness.StoppedUsefulPairLaw.rowSpaceFintype
attribute [local instance] OAI.PerfectCompleteness.StoppedUsefulPairLaw.backgroundFintype
private theorem liftFresh_law (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    (actualLaw rows repeats p chosen q right hrows).pushforward
        (liftFresh rows repeats p chosen q native right projection) =
      (directionLaw rows j hrows).product
        ((WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right).product
          (nativeScalarLaw repeats p chosen q native right projection)) := by
  let μ := WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right
  let ρ := RecursiveSampler.law F2 repeats (.step chosen q) (LeafDomain (cutSlots p right))
  let f := HPullback (CutGroupedProjection.cutProjection p projection)
  change ((directionLaw rows j hrows).product (μ.product ρ)).pushforward
    (fun z => (id z.1, (id z.2.1, f z.2.2))) = _
  rw [FiniteDistribution.product_pushforward (directionLaw rows j hrows) (μ.product ρ)
    id (fun z => (id z.1, f z.2)), FiniteDistribution.pushforward_id,
    FiniteDistribution.product_pushforward μ ρ id f, FiniteDistribution.pushforward_id]
  rfl

private theorem descriptor_chain_law
    {S D E T B V U : Type*}
    [Fintype S] [Fintype D] [Fintype E] [Fintype T]
    [Fintype B] [Fintype V] [Fintype U]
    (μ : FiniteDistribution S) (δ : FiniteDistribution D)
    (τ : FiniteDistribution T) (ν : FiniteDistribution E)
    (β : FiniteDistribution B) (ρ : FiniteDistribution V)
    (κ : FiniteDistribution U)
    (lift : S → D × (T × V))
    (read : T → E × B)
    (transport : D × (B × V) → U)
    (hLift : μ.pushforward lift = δ.product (τ.product ρ))
    (hRead : τ.pushforward read = ν.product β)
    (hTransport : (δ.product (β.product ρ)).pushforward transport = κ) :
    μ.pushforward (fun s =>
      (⟨(read (lift s).2.1).1,
        transport ((lift s).1, ((read (lift s).2.1).2, (lift s).2.2))⟩ : Σ _ : E, U)) =
      CompletionSoundness.sigmaLaw ν (fun _ => κ) := by
  let f : D × (T × V) → D × ((E × B) × V) :=
    fun z => (z.1, (read z.2.1, z.2.2))
  let r : D × ((E × B) × V) → (Σ _ : E, D × (B × V)) :=
    fun z => ⟨z.2.1.1, (z.1, (z.2.1.2, z.2.2))⟩
  let g : (Σ _ : E, D × (B × V)) → (Σ _ : E, U) :=
    fun z => ⟨z.1, transport z.2⟩
  have hInner : (τ.product ρ).pushforward
      (fun z : T × V => (read z.1, z.2)) = (ν.product β).product ρ := by
    simpa only [id_eq, FiniteDistribution.pushforward_id, hRead] using
      FiniteDistribution.product_pushforward τ ρ read (id : V → V)
  have hMap : (δ.product (τ.product ρ)).pushforward f =
      δ.product ((ν.product β).product ρ) := by
    simpa only [f, id_eq, FiniteDistribution.pushforward_id, hInner] using
      FiniteDistribution.product_pushforward δ (τ.product ρ) (id : D → D)
        (fun z : T × V => (read z.1, z.2))
  have hNative : ((μ.pushforward lift).pushforward f).pushforward r =
      CompletionSoundness.sigmaLaw ν (fun _ => δ.product (β.product ρ)) := by
    rw [hLift, hMap]
    exact BucketDescriptorLaw.reorder_law δ ν β ρ
  have hSigma :
      (CompletionSoundness.sigmaLaw ν (fun _ => δ.product (β.product ρ))).pushforward g =
      CompletionSoundness.sigmaLaw ν (fun _ => κ) := by
    calc
      _ = CompletionSoundness.sigmaLaw ν
          (fun _ => (δ.product (β.product ρ)).pushforward transport) :=
        SigmaObservation.pushforward_fiber ν
          (fun _ => δ.product (β.product ρ)) (fun _ => transport)
      _ = _ := congrArg
        (fun laws : E → FiniteDistribution U => CompletionSoundness.sigmaLaw ν laws)
        (funext (fun _ => hTransport))
  calc
    _ = (((μ.pushforward lift).pushforward f).pushforward r).pushforward g :=
      ((FiniteDistribution.pushforward_comp ((μ.pushforward lift).pushforward f) r g).trans
        ((FiniteDistribution.pushforward_comp (μ.pushforward lift) f
          (fun z : D × ((E × B) × V) => g (r z))).trans
          (FiniteDistribution.pushforward_comp μ lift
            (fun z : D × (T × V) => g (r (f z)))))).symm
    _ = (CompletionSoundness.sigmaLaw ν
        (fun _ => δ.product (β.product ρ))).pushforward g :=
      congrArg (fun law : FiniteDistribution (Σ _ : E, D × (B × V)) =>
        law.pushforward g) hNative
    _ = _ := hSigma

theorem observe_law_oai (rows repeats : Nat → Nat) (p : Path branch N (j + 1))
    (chosen : Fin (branch j)) (q : Path branch j i)
    (native right : Slots branch N → Fin t → MixedSupport.Slot)
    (projection : ∀ s a, MixedSupport.Projection (native s a) (right s a))
    (hrows : 0 < rows (j + 1)) :
    (actualLaw rows repeats p chosen q right hrows).pushforward
        (observe rows repeats p chosen q native right projection) =
      HierarchicalUsefulCollision.law native (upperNode p)
        (externalLaw rows repeats p chosen q right)
        (scalarLaw rows repeats p chosen q native right projection)
        (by simpa only [upperNode_height] using hrows) := by
  have h := descriptor_chain_law
    (S := Sample rows repeats p chosen q right)
    (D := BucketSampler.Direction (rows (j + 1)))
    (E := Descriptor rows repeats p chosen q right)
    (T := WholeArraySampler.Tape rows repeats (p.append (.step chosen q)) right)
    (B := BucketSampler.Tape (rows (j + 1)) (H (cutSlots p native)))
    (V := H (cutSlots p native))
    (U := HierarchicalAgreementMean.BucketSample (rows := rows) native (upperNode p))
    (actualLaw rows repeats p chosen q right hrows)
    (directionLaw rows j hrows)
    (WholeArraySampler.tapeLaw rows repeats (p.append (.step chosen q)) right)
    (externalLaw rows repeats p chosen q right)
    (BucketSampler.tapeLaw (rows (j + 1))
      (nativeScalarLaw repeats p chosen q native right projection))
    (nativeScalarLaw repeats p chosen q native right projection)
    (HierarchicalUsefulCollision.bucketLaw native (upperNode p)
      ((nativeScalarLaw repeats p chosen q native right projection).pushforward
        (CutNodeRows.cutRowEquiv p native))
      (by simpa only [upperNode_height] using hrows))
    (liftFresh rows repeats p chosen q native right projection)
    (readout rows repeats p chosen q native right projection)
    (CutNodeRows.bucketSampleEquiv rows p native)
    (liftFresh_law rows repeats p chosen q native right projection hrows)
    (readout_law rows repeats p chosen q native right projection)
    (CutBucketTransportActual.nativeLaw_pushforward rows p native
      (nativeScalarLaw repeats p chosen q native right projection) hrows)
  have hmap : observe rows repeats p chosen q native right projection =
      (fun s : Sample rows repeats p chosen q right =>
        (⟨(readout rows repeats p chosen q native right projection
              (liftFresh rows repeats p chosen q native right projection s).2.1).1,
          CutNodeRows.bucketSampleEquiv rows p native
            ((liftFresh rows repeats p chosen q native right projection s).1,
              ((readout rows repeats p chosen q native right projection
                (liftFresh rows repeats p chosen q native right projection s).2.1).2,
                (liftFresh rows repeats p chosen q native right projection s).2.2))⟩ :
          HierarchicalUsefulCollision.Sample (P := Descriptor rows repeats p chosen q right)
            (rows := rows) native (upperNode p))) := by
    funext s
    rfl
  exact (congrArg (fun f : Sample rows repeats p chosen q right →
      HierarchicalUsefulCollision.Sample (P := Descriptor rows repeats p chosen q right)
        (rows := rows) native (upperNode p) =>
      (actualLaw rows repeats p chosen q right hrows).pushforward f) hmap).trans h

end
end PerfectCompleteness.StoppedUsefulPairLaw

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.StoppedUsefulPairLaw.observe_law_oai := @OAI.PerfectCompleteness.StoppedUsefulPairLaw.observe_law_oai
