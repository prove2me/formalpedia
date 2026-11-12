-- Prove2me | solution 1 for OAI.PerfectCompleteness.CleanNativeReplay.rightArrays_heq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:14.452792+00:00
-- url     : https://prove2.me/submissions/1f6c75a8-fba2-471f-9382-2ce9c288493e

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
import Theorems.Thm_OAI_PerfectCompleteness_CleanNativeReplay_rightReplay_heq

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketSampler

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {Ω H : Type*} [AddCommGroup H] [Module F2 H]

theorem linearMap_evaluate (ℓ : Nat) (eval : Ω → H) (t : Tape ℓ Ω)
    (q : H →ₗ[F2] F2) (i : Fin ℓ) :
    q (evaluate ℓ eval t i) = ∑ v : Direction ℓ, v.val i * q (eval (t v)) := by
  simp only [evaluate, map_sum, map_smul, smul_eq_mul]

theorem evaluate_apply {X : Type*} (ℓ : Nat) (V : Submodule F2 (X → F2))
    (eval : Ω → V) (t : Tape ℓ Ω) (i : Fin ℓ) (x : X) :
    (evaluate ℓ eval t i).val x =
      ∑ v : Direction ℓ, v.val i * (eval (t v)).val x :=
  linearMap_evaluate ℓ eval t (EvaluationMatrix.evaluation V x) i


open PointwiseSpaces RecursiveSpaces DescendantSpaces

universe u

end
end PerfectCompleteness.BucketSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatentSupportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformLatentSupport

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section Latent

variable {S J D : Type*} [Fintype S] [Fintype J] [DecidableEq J] [Fintype D]
  (Ω : S → J → Type*) [∀ s j, Fintype (Ω s j)] [∀ s j, Nonempty (Ω s j)]

theorem latentKernel_weight_zero_of_tag_ne (s : S) (raw : UniformLatent.Raw Ω)
    (hne : raw.1 ≠ s) : (UniformLatent.latentKernel Ω s).weight raw = 0 := by
  simp only [UniformLatent.latentKernel, FiniteDistribution.pushforward]
  apply Finset.sum_eq_zero
  intro x _
  have hx : (⟨s, x⟩ : UniformLatent.Raw Ω) ≠ raw := by
    intro h
    exact hne (congrArg (fun z : UniformLatent.Raw Ω => z.1) h).symm
  simp only [ite_eq_right hx]

theorem latentKernel_tag (s : S) (raw : UniformLatent.Raw Ω)
    (hraw : (UniformLatent.latentKernel Ω s).weight raw ≠ 0) : raw.1 = s := by
  by_contra hne
  exact hraw (latentKernel_weight_zero_of_tag_ne Ω s raw hne)

theorem projectedKernel_weight_inr (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D) (s : S) (raw : UniformLatent.Raw Ω) :
    (UniformLatent.projectedKernel Ω flag nonprojected s).weight (Sum.inr raw) =
      flag.weight true * (UniformLatent.latentKernel Ω s).weight raw := by
  simp [UniformLatent.projectedKernel, FiniteDistribution.mixture,
    FiniteDistribution.pushforward]

theorem projectedKernel_tag (flag : FiniteDistribution Bool)
    (nonprojected : S → FiniteDistribution D) (s : S) (raw : UniformLatent.Raw Ω)
    (hraw : (UniformLatent.projectedKernel Ω flag nonprojected s).weight (Sum.inr raw) ≠ 0) :
    raw.1 = s := by
  apply latentKernel_tag Ω s raw
  intro hz
  apply hraw
  rw [projectedKernel_weight_inr, hz, mul_zero]

end Latent


variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J D : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)] [∀ i, Fintype (D i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (J i)] [∀ i, DecidableEq (D i)]
  (Ω : (i : I) → (E i × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]
  (μ : (i : I) → FiniteDistribution (E i))
  (ν : (i : I) → FiniteDistribution (R i))
  (flag : (i : I) → FiniteDistribution Bool)
  (nonprojected : (i : I) → E i × R i → FiniteDistribution (D i))

omit [Fintype I] [DecidableEq I] [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (D i)] [∀ i s j, DecidableEq (Ω i s j)] in
theorem childLaw_weight (i : I)
    (x : E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i)) :
    (childLaw Ω μ ν flag nonprojected i).weight x =
      (μ i).weight x.1 * ((ν i).weight x.2.1 *
        (UniformLatent.projectedKernel (Ω i) (flag i) (nonprojected i) (x.1, x.2.1)).weight
          x.2.2) := rfl

omit [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)]
  [∀ i, DecidableEq (D i)] [∀ i s j, DecidableEq (Ω i s j)] in
theorem childrenLaw_child_weight_ne_zero
    (x : (i : I) → E i × (R i × UniformCleanSources.ChildRaw (D := D) Ω i))
    (hx : (UniformCleanSources.childrenLaw Ω μ ν flag nonprojected).weight x ≠ 0)
    (i : I) : (childLaw Ω μ ν flag nonprojected i).weight (x i) ≠ 0 := by
  intro hz
  apply hx
  change (∏ j, (childLaw Ω μ ν flag nonprojected j).weight (x j)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ i) hz

end
end PerfectCompleteness.UniformLatentSupport



namespace PerfectCompleteness.NativeTaggedUniform

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section Native

variable {S : Type*} [Fintype S] [DecidableEq S]
  (Native : S → Type*) [∀ s, Fintype (Native s)] [∀ s, Nonempty (Native s)]

omit [DecidableEq S] in
theorem kernel_weight_zero_of_tag_ne (s : S) (raw : Raw Native) (hne : raw.1 ≠ s) :
    (kernel Native s).weight raw = 0 := by
  unfold kernel FiniteDistribution.pushforward
  apply Finset.sum_eq_zero
  intro x _
  have hx : (⟨s, x⟩ : Raw Native) ≠ raw := by
    intro h
    exact hne (congrArg (fun z : Raw Native => z.1) h).symm
  exact ite_eq_right hx

theorem kernel_tag (s : S) (raw : Raw Native)
    (hraw : (kernel Native s).weight raw ≠ 0) : raw.1 = s := by
  by_contra hne
  exact hraw (kernel_weight_zero_of_tag_ne Native s raw hne)

end Native

section Projection

variable {S J : Type*} [Fintype S] [DecidableEq S] [Fintype J] [DecidableEq J]
  (Native : S → Type*) [∀ s, Fintype (Native s)] [∀ s, Nonempty (Native s)]
  (Ω : S → J → Type*) [∀ s j, Fintype (Ω s j)] [∀ s j, Nonempty (Ω s j)]

theorem projectedKernel_weight_inl (flag : FiniteDistribution Bool) (s : S)
    (raw : Raw Native) :
    (UniformLatent.projectedKernel Ω flag (kernel Native) s).weight (.inl raw) =
      flag.weight false * (kernel Native s).weight raw := by
  simp [UniformLatent.projectedKernel, FiniteDistribution.mixture,
    FiniteDistribution.pushforward]

theorem projectedKernel_sourceTag (flag : FiniteDistribution Bool) (s : S)
    (raw : Raw Native ⊕ UniformLatent.Raw Ω)
    (hraw : (UniformLatent.projectedKernel Ω flag (kernel Native) s).weight raw ≠ 0) :
    sourceTag Native Ω raw = s := by
  cases raw with
  | inl raw =>
      apply kernel_tag Native s raw
      intro hz
      apply hraw
      rw [projectedKernel_weight_inl, hz, mul_zero]
  | inr raw =>
      exact UniformLatentSupport.projectedKernel_tag Ω flag (kernel Native) s raw hraw

end Projection


variable {I : Type*} [Fintype I] [DecidableEq I]
  {E R J : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, Fintype (R i)] [∀ i, Fintype (J i)]
  [∀ i, DecidableEq (E i)] [∀ i, DecidableEq (R i)] [∀ i, DecidableEq (J i)]
  (Native : (i : I) → E i × R i → Type*)
  [∀ i s, Fintype (Native i s)] [∀ i s, Nonempty (Native i s)]
  (Ω : (i : I) → (E i × R i) → J i → Type*)
  [∀ i s j, Fintype (Ω i s j)] [∀ i s j, Nonempty (Ω i s j)]
  [∀ i s j, DecidableEq (Ω i s j)]
  (μ : (i : I) → FiniteDistribution (E i))
  (ν : (i : I) → FiniteDistribution (R i))
  (flag : (i : I) → FiniteDistribution Bool)

omit [Fintype I] [DecidableEq I] [∀ i s j, DecidableEq (Ω i s j)] in
theorem childLaw_sourceTag (i : I)
    (x : E i × (R i × UniformCleanSources.ChildRaw (D := fun i => Raw (Native i)) Ω i))
    (hx : (UniformLatentSupport.childLaw Ω μ ν flag (fun i => kernel (Native i)) i).weight
      x ≠ 0) :
    sourceTag (Native i) (Ω i) x.2.2 = (x.1, x.2.1) := by
  apply projectedKernel_sourceTag (Native i) (Ω i) (flag i) (x.1, x.2.1) x.2.2
  intro hz
  apply hx
  rw [UniformLatentSupport.childLaw_weight, hz, mul_zero, mul_zero]

omit [∀ i s j, DecidableEq (Ω i s j)] in
theorem childrenLaw_sourceTag
    (x : (i : I) → E i ×
      (R i × UniformCleanSources.ChildRaw (D := fun i => Raw (Native i)) Ω i))
    (hx : (UniformCleanSources.childrenLaw Ω μ ν flag (fun i => kernel (Native i))).weight
      x ≠ 0) (i : I) :
    sourceTag (Native i) (Ω i) (x i).2.2 = ((x i).1, (x i).2.1) :=
  childLaw_sourceTag Native Ω μ ν flag i (x i)
    (UniformLatentSupport.childrenLaw_child_weight_ne_zero Ω μ ν flag
      (fun i => kernel (Native i)) x hx i)

end
end PerfectCompleteness.NativeTaggedUniform



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceChildKernelLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceChildKernel

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces PointwiseSpaces HierarchicalArrays
open SourceQuestionReconstruction

noncomputable section

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem projectedEquiv_zero (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i) :
    projectedEquiv (C := C) (t := t) rows clauses designated i s (zero (C := C) (t := t) rows clauses designated i s) =
      zeroBlock rows (ProjectedCardinality.projectedSlots (ids clauses designated i s)) := rfl

theorem decodeRight_clean (i : Fin (branch n)) (s : Source (m := m) (t := t) designated i)
    (raw : Raw (C := C) (t := t) rows clauses designated i)
    (htag : rawTag rows clauses designated i raw = s)
    (hclean : UniformLatent.projectedZero (Factors (C := C) (t := t) rows clauses designated i)
      (zero (C := C) (t := t) rows clauses designated i) raw = true) :
    decodeRight rows clauses designated i s raw =
      zeroBlock rows (mixedSlots clauses designated i s
        (rawProjected rows clauses designated i raw)) := by
  cases raw with
  | inl raw =>
      simp only [UniformLatent.projectedZero, Bool.false_eq_true] at hclean
  | inr raw =>
      rcases raw with ⟨tag, values⟩
      change tag = s at htag
      subst tag
      change decide (∀ j, values j = zero (C := C) (t := t) rows clauses designated i s j) = true at hclean
      have hvalues : values = zero (C := C) (t := t) rows clauses designated i s :=
        funext (of_decide_eq_true hclean)
      change decodeProjected rows clauses designated i s ⟨s, values⟩ = _
      rw [hvalues, decodeProjected_tagged]
      exact projectedEquiv_zero (C := C) (t := t) rows clauses designated i s

theorem childrenLaw_tag (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) → FiniteDistribution (Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hx : (childrenLaw rows clauses designated μ ν flag).weight x ≠ 0) (i : Fin (branch n)) :
    rawTag rows clauses designated i (x i).2.2 = ((x i).1, (x i).2.1) :=
  NativeTaggedUniform.childrenLaw_sourceTag
    (Native (C := C) (t := t) rows clauses designated) (Factors (C := C) (t := t) rows clauses designated)
    μ ν flag x hx i

theorem childrenLaw_clean_zero
    (μ : Fin (branch n) → FiniteDistribution (SourceTuple m t))
    (ν : (i : Fin (branch n)) → FiniteDistribution (Rest (m := m) (t := t) designated i))
    (flag : Fin (branch n) → FiniteDistribution Bool)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hx : (childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (i : Fin (branch n))
    (hclean : UniformCleanSources.childClean (Factors (C := C) (t := t) rows clauses designated)
      (zero (C := C) (t := t) rows clauses designated) i (x i).1 (x i).2.1 (x i).2.2 = true) :
    decodeRight rows clauses designated i ((x i).1, (x i).2.1) (x i).2.2 =
      zeroBlock rows (mixedSlots clauses designated i ((x i).1, (x i).2.1)
        (rawProjected rows clauses designated i (x i).2.2)) :=
  decodeRight_clean rows clauses designated i ((x i).1, (x i).2.1) (x i).2.2
    (childrenLaw_tag rows clauses designated μ ν flag x hx i) hclean

end
end PerfectCompleteness.SourceChildKernel

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

theorem evaluate_refl (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (A : Slots branch (m + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.refl (m + 1)) A) :
    CutSamplerRefinement.evaluate 𝕜 repeats (.refl (m + 1)) A tape =
      UniformChildSum.recursiveSum A (tape ()) := rfl

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

theorem zeroAtClean_iff (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      (∀ terminal i, clean i →
        (CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal i = 0) ↔
      CutSamplerLocality.ZeroAtClean 𝕜 repeats p A clean tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape
          constructor
          · intro hzero i hi
            exact hzero () i hi
          · intro hzero terminal i hi
            cases terminal
            exact hzero i hi
      | step i p =>
          intro A clean tape
          constructor
          · intro hzero h b
            apply (ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).mp
            intro terminal j hj
            apply Subtype.ext
            have hread := congrArg
              (fun f : CutTerminalSplit.TerminalFactor 𝕜 (.step i p) A => (f j).val)
              (splitTape_terminal_step 𝕜 repeats i p A tape h b terminal)
            exact hread.symm.trans (congrArg Subtype.val (hzero ((h, b), terminal) j hj))
          · intro hzero terminal j hj
            rcases terminal with ⟨⟨h, b⟩, terminal⟩
            have hsub := (ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).mpr (hzero h b)
            apply Subtype.ext
            have hread := congrArg
              (fun f : CutTerminalSplit.TerminalFactor 𝕜 (.step i p) A => (f j).val)
              (splitTape_terminal_step 𝕜 repeats i p A tape h b terminal)
            exact hread.trans (congrArg Subtype.val (hsub terminal j hj))

end
end PerfectCompleteness.CutTerminalZero

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutExteriorTransportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutZero

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n m t : Nat}

theorem grouped_step_iff (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots) :
    GroupedAtClean rows repeats (.step i p) slots clean tape ↔
      (∀ bucket terminal child, clean child →
        (CutTerminalSplit.splitTape F2 repeats (.step i p)
          (LeafDomain slots) (tape.1 bucket)).1 terminal child = 0) ∧
      GroupedAtClean rows repeats p (childSlots slots i) clean tape.2.1 := by
  constructor
  · intro h
    constructor
    · intro bucket terminal child hchild
      exact (h child hchild).1 (.inl (bucket, terminal))
    · intro child hchild
      exact ⟨fun q => (h child hchild).1 (.inr q), (h child hchild).2⟩
  · rintro ⟨hroot, hselected⟩ child hchild
    refine ⟨?_, (hselected child hchild).2⟩
    intro q
    rcases q with ⟨bucket, terminal⟩ | q
    · exact hroot bucket terminal child hchild
    · exact (hselected child hchild).1 q

theorem grouped_iff (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots),
      GroupedAtClean rows repeats p slots clean tape ↔
        ZeroAtClean rows repeats p slots clean tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots clean tape
          rfl
      | step i p =>
          intro slots clean tape
          rw [grouped_step_iff]
          exact and_congr
            (forall_congr' (fun bucket =>
              CutTerminalZero.zeroAtClean_iff F2 repeats (.step i p)
                (LeafDomain slots) clean (tape.1 bucket)))
            (ih p (childSlots slots i) clean tape.2.1)

end PerfectCompleteness.WholeCutZero

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerKeyLocalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.CutSamplerReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem evaluate_refl (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (A : Slots branch (m + 1) → Type u) (clean : Fin (branch m) → Prop)
    (tape : Tape 𝕜 repeats (.refl (m + 1)) A clean) (x : Assignment A) :
    evaluate 𝕜 repeats (.refl (m + 1)) A clean tape x =
      ∑ i : {i : Fin (branch m) // ¬ clean i}, (tape i).val (childRestriction A i.val x) := rfl

theorem evaluate_step (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u) (clean : Fin (branch m) → Prop)
    (tape : Tape 𝕜 repeats (.step i p) A clean) (x : Assignment A) :
    evaluate 𝕜 repeats (.step i p) A clean tape x =
      (∑ j : OffPath i, (tape.1 j).val (childRestriction A j.val x)) +
        ∑ h : Fin (repeats (n + 1)),
          evaluate 𝕜 repeats p (childFamily A i) clean (tape.2 (h, false)) (childRestriction A i x) *
            evaluate 𝕜 repeats p (childFamily A i) clean (tape.2 (h, true))
              (childRestriction A i x) := rfl

theorem evaluate_erase (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      CutSamplerLocality.ZeroAtClean 𝕜 repeats p A clean tape →
      ∀ x : Assignment A,
        evaluate 𝕜 repeats p A clean (erase 𝕜 repeats p A clean tape) x =
          (CutSamplerRefinement.evaluate 𝕜 repeats p A tape).val x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape hzero x
          have heval :
              (UniformChildSum.recursiveSum (𝕜 := 𝕜) A (tape ())).val x =
                ∑ i : Fin (branch n), (tape () i).val (childRestriction A i x) := by
            have hsum := congrFun
              (UniformChildSum.childSum_apply (𝕜 := 𝕜) (childRestriction A)
                (fun i => space 𝕜 branch n (childFamily A i)) (tape ())) x
            simp only [Finset.sum_apply, PointwiseSpaces.pullback_apply] at hsum
            refine hsum.trans ?_
            refine Finset.sum_congr (ι := Fin (branch n)) ?_ ?_
            · ext i
              simp only [Finset.mem_univ]
            · intro i _
              rfl
          rw [evaluate_refl, CutSamplerLocality.evaluate_refl, heval]
          simp only [erase]
          rw [← Fintype.sum_subtype_add_sum_subtype clean
            (fun i => (tape () i).val (childRestriction A i x))]
          have hz : (∑ i : {i : Fin (branch n) // clean i},
              (tape () i.val).val (childRestriction A i.val x)) = 0 := by
            apply Finset.sum_eq_zero
            intro i _
            rw [hzero i.val i.property]
            rfl
          rw [hz, zero_add]
      | step i p =>
          intro A clean tape hzero x
          rw [evaluate_step, CutSamplerLocality.evaluate_step]
          simp only [erase, RecursiveSampler.combine, RecursiveSampler.combineFunction,
            Finset.sum_apply, Pi.add_apply, Pi.mul_apply, PointwiseSpaces.pullback_apply]
          apply congrArg (fun z =>
            (∑ j : OffPath i, (tape (.inl j)).val (childRestriction A j.val x)) + z)
          apply Finset.sum_congr rfl
          intro h _
          rw [ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h false) (hzero h false),
            ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h true) (hzero h true)]

end
end PerfectCompleteness.CutSamplerReplay



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_WholeCutLocalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutLocality

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluate_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots) (node : Nodes branch n) :
    WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inr (i, node)) =
      WholeCutSampler.evaluate rows repeats p (childSlots slots i) tape.2.1 node := by
  unfold WholeCutSampler.evaluate
  rw [WholeArraySampler.evaluate_selected]
  rfl

theorem evaluate_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inr (j.val, node)) =
      tape.2.2 j node := by
  unfold WholeCutSampler.evaluate
  rw [WholeArraySampler.evaluate_ordinary]
  rfl

end
end PerfectCompleteness.WholeCutLocality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluate_refl_child (rows repeats : Nat → Nat)
    (slots : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.refl (m + 1)) slots clean) (x : Domain slots)
    (i : Fin (branch m)) (node : Nodes branch m) (row : Fin (rows (Nodes.height node))) :
    evaluate rows repeats (.refl (m + 1)) slots clean tape x (.inr (i, node)) row =
      if hi : ¬ clean i then
        ((tape ⟨i, hi⟩).2 node row).val
          (restrictNode (childSlots slots i) node (restrictChild slots i x))
      else 0 := rfl

theorem evaluate_step_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) (x : Domain slots)
    (row : Fin (rows (n + 1))) :
    evaluate rows repeats (.step i p) slots clean tape x (.inl ()) row =
      ∑ bucket : BucketSampler.Direction (rows (n + 1)), bucket.val row *
        CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots)
          clean (tape.1 bucket) x := rfl

theorem evaluate_step_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) (x : Domain slots)
    (node : Nodes branch n) (row : Fin (rows (Nodes.height node))) :
    evaluate rows repeats (.step i p) slots clean tape x (.inr (i, node)) row =
      evaluate rows repeats p (childSlots slots i) clean tape.2.1
        (restrictChild slots i x) node row := by
  simp only [evaluate]
  exact dite_eq_left True.intro

theorem evaluate_step_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) (x : Domain slots)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n)
    (row : Fin (rows (Nodes.height node))) :
    evaluate rows repeats (.step i p) slots clean tape x (.inr (j.val, node)) row =
      ((tape.2.2 j) node row).val
        (restrictNode (childSlots slots j.val) node (restrictChild slots j.val x)) := by
  simp only [evaluate, dite_eq_right j.property]

theorem evaluate_erase (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (tape : WholeCutSampler.Tape rows repeats p slots),
      WholeCutZero.ZeroAtClean rows repeats p slots clean tape →
      ∀ x : Domain slots,
        evaluate rows repeats p slots clean (erase rows repeats p slots clean tape) x =
          joint (WholeCutSampler.evaluate rows repeats p slots tape) x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots clean tape hzero x
          funext node row
          rcases node with u | ⟨i, node⟩
          · cases u
            let scalarTape : CutSamplerRefinement.Tape F2 repeats (.refl (n + 1))
                (LeafDomain slots) := fun _ i => (tape i).1 row
            have hz : CutSamplerLocality.ZeroAtClean F2 repeats (.refl (n + 1))
                (LeafDomain slots) clean scalarTape :=
              fun i hi => (hzero i hi).1 row
            exact CutSamplerReplay.evaluate_erase F2 repeats (.refl (n + 1))
              (LeafDomain slots) clean scalarTape hz x
          · refine (evaluate_refl_child rows repeats slots clean
              (erase rows repeats (.refl (n + 1)) slots clean tape) x i node row).trans ?_
            change (if hi : ¬ clean i then
                ((tape i).2 node row).val
                  (restrictNode (childSlots slots i) node (restrictChild slots i x))
                else 0) =
              ((tape i).2 node row).val
                (restrictNode (childSlots slots i) node (restrictChild slots i x))
            by_cases hi : clean i
            · rw [dite_eq_right (not_not_intro hi), (hzero i hi).2 node row]
              rfl
            · rw [dite_eq_left hi]
      | step i p =>
          intro slots clean tape hzero x
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            refine (evaluate_step_root rows repeats i p slots clean
              (erase rows repeats (.step i p) slots clean tape) x row).trans ?_
            change (∑ bucket : BucketSampler.Direction (rows (n + 1)), bucket.val row *
                CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots) clean
                  (CutSamplerReplay.erase F2 repeats (.step i p) (LeafDomain slots)
                    clean (tape.1 bucket)) x) =
              (WholeCutSampler.evaluate rows repeats (.step i p) slots tape (.inl ()) row).val x
            have heval := BucketSampler.evaluate_apply (rows (n + 1))
              (space F2 branch (n + 1) (LeafDomain slots))
              (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain slots))
              tape.1 row x
            refine Eq.trans ?_ heval.symm
            refine Finset.sum_congr (ι := BucketSampler.Direction (rows (n + 1))) ?_ ?_
            · ext bucket
              simp only [Finset.mem_univ]
            · intro bucket _
              exact congrArg (fun z : F2 => bucket.val row * z)
                (CutSamplerReplay.evaluate_erase F2 repeats (.step i p)
                  (LeafDomain slots) clean (tape.1 bucket) (hzero.1 bucket) x)
          · by_cases hji : j = i
            · subst j
              refine (evaluate_step_selected rows repeats i p slots clean
                (erase rows repeats (.step i p) slots clean tape) x node row).trans ?_
              exact (congrFun (congrFun
                (ih p (childSlots slots i) clean tape.2.1 hzero.2
                  (restrictChild slots i x)) node) row).trans
                (congrArg
                  (fun block : Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots i) node) =>
                    (block row).val
                      (restrictNode (childSlots slots i) node (restrictChild slots i x)))
                  (WholeCutLocality.evaluate_selected rows repeats i p slots tape node)).symm
            · refine (evaluate_step_ordinary rows repeats i p slots clean
                (erase rows repeats (.step i p) slots clean tape) x ⟨j, hji⟩ node row).trans ?_
              exact (congrArg
                (fun block : Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots j) node) =>
                  (block row).val
                    (restrictNode (childSlots slots j) node (restrictChild slots j x)))
                (WholeCutLocality.evaluate_ordinary rows repeats i p slots tape ⟨j, hji⟩ node)).symm

end
end PerfectCompleteness.WholeCutReplay

end

section

namespace PerfectCompleteness.CutSamplerReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces RecursiveSampler PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem evaluateSpace_apply (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : Tape 𝕜 repeats p A clean) (x : Assignment A),
      (evaluateSpace 𝕜 repeats p A clean tape).val x =
        evaluate 𝕜 repeats p A clean tape x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape x
          exact retainedSum_apply 𝕜 A clean tape x
      | step i p =>
          intro A clean tape x
          rw [evaluateSpace, evaluate_step]
          simp only [RecursiveSampler.combine, RecursiveSampler.combineFunction,
            Finset.sum_apply, Pi.add_apply, Pi.mul_apply, PointwiseSpaces.pullback_apply]
          apply congrArg (fun z =>
            (∑ j : OffPath i, (tape.1 j).val (childRestriction A j.val x)) + z)
          apply Finset.sum_congr rfl
          intro h _
          rw [ih p (childFamily A i) clean (tape.2 (h, false)),
            ih p (childFamily A i) clean (tape.2 (h, true))]

end
end PerfectCompleteness.CutSamplerReplay

namespace PerfectCompleteness.HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem joint_injective
    (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
    (rows : Nat → Nat) :
    Function.Injective (joint (slots := slots) (rows := rows)) := by
  intro a b hab
  funext node row
  apply Subtype.ext
  funext x
  obtain ⟨global, rfl⟩ := restrictNode_surjective slots node x
  exact congrFun (congrFun (congrFun hab global) node) row

end
end PerfectCompleteness.HierarchicalArrays

namespace PerfectCompleteness.WholeCutReplay

open scoped BigOperators Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluateArrays_step_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean) (node : Nodes branch n) :
    evaluateArrays rows repeats (.step i p) slots clean tape (.inr (i, node)) =
      evaluateArrays rows repeats p (childSlots slots i) clean tape.2.1 node := by
  exact congrFun (WholeArraySampler.childrenAt_selected slots rows i
    (evaluateArrays rows repeats p (childSlots slots i) clean tape.2.1) tape.2.2) node

theorem evaluateArrays_step_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (tape : Tape rows repeats (.step i p) slots clean)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    evaluateArrays rows repeats (.step i p) slots clean tape (.inr (j.val, node)) =
      tape.2.2 j node := by
  exact congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
    (evaluateArrays rows repeats p (childSlots slots i) clean tape.2.1) tape.2.2 j) node

theorem joint_evaluateArrays_apply (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop) (tape : Tape rows repeats p slots clean)
      (x : Domain slots),
      joint (evaluateArrays rows repeats p slots clean tape) x =
        evaluate rows repeats p slots clean tape x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots clean tape x
          funext node row
          rcases node with u | ⟨i, node⟩
          · cases u
            exact CutSamplerReplay.evaluateSpace_apply F2 repeats (.refl (n + 1))
              (LeafDomain slots) clean (fun i => (tape i).1 row) x
          · change
              (((if hi : ¬ clean i then (tape ⟨i, hi⟩).2 else fun _ _ => 0) :
                Arrays (childSlots slots i) rows) node row).val
                  (restrictNode (childSlots slots i) node (restrictChild slots i x)) =
                (if hi : ¬ clean i then
                  ((tape ⟨i, hi⟩).2 node row).val
                    (restrictNode (childSlots slots i) node (restrictChild slots i x))
                else 0)
            by_cases hi : ¬ clean i
            · simp only [dite_eq_left hi]
            · simp only [dite_eq_right hi]
              rfl
      | step i p =>
          intro slots clean tape x
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            change (BucketSampler.evaluate (rows (n + 1))
                (CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean)
                tape.1 row).val x =
              ∑ bucket : BucketSampler.Direction (rows (n + 1)), bucket.val row *
                CutSamplerReplay.evaluate F2 repeats (.step i p) (LeafDomain slots)
                  clean (tape.1 bucket) x
            have heval := BucketSampler.evaluate_apply (rows (n + 1))
              (space F2 branch (n + 1) (LeafDomain slots))
              (CutSamplerReplay.evaluateSpace F2 repeats (.step i p) (LeafDomain slots) clean)
              tape.1 row x
            refine heval.trans ?_
            refine Finset.sum_congr (ι := BucketSampler.Direction (rows (n + 1))) ?_ ?_
            · ext bucket
              simp only [Finset.mem_univ]
            · intro bucket _
              exact congrArg (fun z : F2 => bucket.val row * z)
                (CutSamplerReplay.evaluateSpace_apply F2 repeats (.step i p)
                  (LeafDomain slots) clean (tape.1 bucket) x)
          · by_cases hji : j = i
            · subst j
              exact (congrArg
                (fun block : Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots i) node) =>
                  (block row).val
                    (restrictNode (childSlots slots i) node (restrictChild slots i x)))
                (evaluateArrays_step_selected rows repeats i p slots clean tape node)).trans
                  ((congrFun (congrFun
                    (ih p (childSlots slots i) clean tape.2.1 (restrictChild slots i x)) node) row).trans
                    (evaluate_step_selected rows repeats i p slots clean tape x node row).symm)
            · exact (congrArg
                (fun block : Fin (rows (Nodes.height node)) → H (nodeSlots (childSlots slots j) node) =>
                  (block row).val
                    (restrictNode (childSlots slots j) node (restrictChild slots j x)))
                (evaluateArrays_step_ordinary rows repeats i p slots clean tape ⟨j, hji⟩ node)).trans
                  (evaluate_step_ordinary rows repeats i p slots clean tape x ⟨j, hji⟩ node row).symm

theorem evaluateArrays_erase (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.ZeroAtClean rows repeats p slots clean tape) :
    evaluateArrays rows repeats p slots clean (erase rows repeats p slots clean tape) =
      WholeCutSampler.evaluate rows repeats p slots tape := by
  apply HierarchicalArrays.joint_injective slots rows
  funext x
  rw [joint_evaluateArrays_apply]
  exact evaluate_erase rows repeats p slots clean tape hzero x

theorem evaluateArrays_erase_of_grouped_zero (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots)
    (hzero : WholeCutZero.GroupedAtClean rows repeats p slots clean tape) :
    evaluateArrays rows repeats p slots clean (erase rows repeats p slots clean tape) =
      WholeCutSampler.evaluate rows repeats p slots tape :=
  evaluateArrays_erase rows repeats p slots clean tape
    ((WholeCutZero.grouped_iff rows repeats p slots clean tape).mp hzero)

end
end PerfectCompleteness.WholeCutReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanRecordChildBlocks
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanRecordChildBlocks

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open SourceQuestionReconstruction

variable {branch : Nat → Nat} {h t v m : Nat} {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

variable [NeZero m]

omit [NeZero m] in
theorem childClean_of_clean (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true) (i : Fin (branch h))
    (hi : clean rows clauses designated record i) :
    UniformCleanSources.childClean
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
      i (x i).1 (x i).2.1 (x i).2.2 = true := by
  have obs := CleanSourceRecord.observation_eq designated
    (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
    (SourceChildKernel.zero (C := C) (t := t) rows clauses designated) record x hevent i
  cases hc : UniformCleanSources.childClean
      (SourceChildKernel.Factors (C := C) (t := t) rows clauses designated)
      (SourceChildKernel.zero (C := C) (t := t) rows clauses designated)
      i (x i).1 (x i).2.1 (x i).2.2 with
  | false =>
      have hr : record i = .inl (x i) := by
        simpa only [SelectedSources.childObservation, hc, Bool.false_eq_true, ite_false, if_false]
          using obs.symm
      simp only [clean, CleanSourceRecord.clean, hr, UniformCleanSources.cleanRecord,
        Bool.false_eq_true] at hi
  | true => rfl

end
end PerfectCompleteness.CleanRecordChildBlocks

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanPhysicalReplay

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {branch : Nat → Nat} {root h t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)

private theorem cast_zeroBlock {n : Nat} {C : Type*} [Fintype C]
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target) :
    cast (congrArg (SourceChildKernel.Block C rows) hs)
        (SourceChildKernel.zeroBlock (C := C) rows slots) =
      SourceChildKernel.zeroBlock rows target := by
  cases hs
  rfl

theorem fillChild_zero (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h)) :
    fillChild rows repeats p outside inside i
        (SourceChildKernel.zeroBlock rows (childSlots inside i)) =
      SourceChildKernel.zeroBlock rows
        (childSlots (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) i) :=
  cast_zeroBlock rows _ _ (childSlots_fill p outside inside i).symm

theorem physicalTape_grouped_zero
    (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows)
    (hzero : ∀ i, clean i → children i =
      SourceChildKernel.zeroBlock rows (childSlots inside i)) :
    WholeCutZero.GroupedAtClean rows repeats p (CutSlotAssembly.fill p outside inside) clean
      (physicalTape rows repeats p outside placeholder inside external children) := by
  intro i hi
  have hz : fillChild rows repeats p outside inside i (children i) =
      SourceChildKernel.zeroBlock rows
        (childSlots (WholeCutGrouping.cutSlots p (CutSlotAssembly.fill p outside inside)) i) := by
    rw [hzero i hi]
    exact fillChild_zero rows repeats p outside inside i
  change (∀ q, ((WholeCutGrouping.splitTape rows repeats p
      (CutSlotAssembly.fill p outside inside)
      (physicalTape rows repeats p outside placeholder inside external children)).2 i).1 q = 0) ∧ _
  simp only [physicalTape, Equiv.apply_symm_apply]
  rw [hz]
  exact ⟨fun _ => rfl, fun _ _ => rfl⟩

section Source

variable {v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

variable
  (μ : Fin (branch h) → FiniteDistribution (SourceQuestionReconstruction.SourceTuple m t))
  (ν : (i : Fin (branch h)) → FiniteDistribution
    (SourceChildKernel.Rest (m := m) (t := t) designated i))
  (flag : Fin (branch h) → FiniteDistribution Bool)

omit [NeZero m] in
theorem rightBlocks_zero (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hx : (SourceChildKernel.childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (i : Fin (branch h)) (hi : CleanRecordChildBlocks.clean rows clauses designated record i) :
    rightBlocks rows repeats p clauses designated x i =
      SourceChildKernel.zeroBlock rows
        (childSlots (rightInside rows repeats p clauses designated x) i) :=
  SourceChildKernel.childrenLaw_clean_zero rows clauses designated μ ν flag x hx i
    (CleanRecordChildBlocks.childClean_of_clean rows clauses designated record x hevent i hi)

omit [NeZero m] in
theorem rightTape_grouped_zero (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hx : (SourceChildKernel.childrenLaw rows clauses designated μ ν flag).weight x ≠ 0)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutZero.GroupedAtClean rows repeats p
      (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (rightTape rows repeats p outside placeholder clauses designated x external) :=
  physicalTape_grouped_zero rows repeats p outside placeholder _ _ external _
    (rightBlocks_zero rows repeats p clauses designated μ ν flag record x hx hevent)

end Source

end
end PerfectCompleteness.CleanPhysicalReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanNativeReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanNativeReplay

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

section Transport

variable {branch : Nat → Nat} {n h t : Nat}

private theorem evaluateArrays_heq (rows repeats : Nat → Nat)
    (p : Path branch n (h + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop) (hs : slots = target)
    (tape : WholeCutReplay.Tape rows repeats p slots clean)
    (other : WholeCutReplay.Tape rows repeats p target clean) (htape : HEq tape other) :
    HEq (WholeCutReplay.evaluateArrays rows repeats p slots clean tape)
      (WholeCutReplay.evaluateArrays rows repeats p target clean other) := by
  cases hs
  cases htape
  rfl

end Transport

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

variable (cube : Nat) (hcube : 0 < cube)

theorem right_grouped_zero (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    WholeCutZero.GroupedAtClean rows repeats (CleanDecoderRate.path S) (rightSlots S x)
      (context S x).clean (rightTape S x) :=
  CleanPhysicalReplay.rightTape_grouped_zero rows repeats (CleanDecoderRate.path S)
    S.outside S.placeholder S.clauses S.designated
    (fun _ => SourceOddLists.tupleLaw m t)
    (fun i => FiniteProduct.law
      (fun _ : {leaf : Slots branch h // leaf ≠ S.designated i} => SourceOddLists.tupleLaw m t))
    (fun _ => ProjectedCleanRate.projectionFlag cube hcube)
    (CleanDecoderRate.observations S x) x hx
    (CleanRecordDecoderInput.event_observe rows repeats upper d S.cut S.clauses S.designated x)
    S.exterior

theorem rightArrays_heq_oai (x : CleanDecoderRate.Sample S)
    (hx : (CleanDecoderRate.rawLaw S cube hcube).weight x ≠ 0) :
    HEq (CleanRightDecoder.arrays (context S x).clauses (context S x).designated
      (context S x).clean (context S x).visible (context S x).projected upper
      (CleanDecoderContext.lower (context S x)) (context S x).cut
      (CleanDecoderContext.lowerHeight upper d) (context S x).outside rows repeats
      (context S x).rightTape (rightOwn S x))
      (WholeCutSampler.evaluate rows repeats (CleanDecoderRate.path S) (rightSlots S x)
        (rightTape S x)) := by
  have h := evaluateArrays_heq rows repeats (CleanDecoderRate.path S)
    (CleanDecoderContext.rightSlots (context S x) (rightOwn S x)) (rightSlots S x)
    (context S x).clean (rightSlots_eq S x) _ _ (rightReplay_heq S x)
  exact h.trans (heq_of_eq (WholeCutReplay.evaluateArrays_erase_of_grouped_zero
    rows repeats (CleanDecoderRate.path S) (rightSlots S x) (context S x).clean
    (rightTape S x) (right_grouped_zero S cube hcube x hx)))

end
end PerfectCompleteness.CleanNativeReplay

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.CleanNativeReplay.rightArrays_heq_oai := @OAI.PerfectCompleteness.CleanNativeReplay.rightArrays_heq_oai
