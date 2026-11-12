-- Prove2me | solution 1 for OAI.PerfectCompleteness.UpperScalarCutProjection.pairRecord_pullback
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:28:17.34014+00:00
-- url     : https://prove2.me/submissions/d0f3c60a-8cbe-4dc5-a34e-09a276b4c337

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

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecordSeedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSampler

open PointwiseSpaces RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

variable (𝕜 : Type w) [Field 𝕜]

noncomputable section

theorem evaluate_step (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    (t : Tape 𝕜 repeats (.step i p) A) :
    evaluate 𝕜 repeats (.step i p) A t =
      combine 𝕜 A i (repeats (n + 1)) (fun j => t (.inl j))
        (fun h => evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A t h false))
        (fun h => evaluate 𝕜 repeats p (childFamily A i)
          (subTape 𝕜 repeats i p A t h true)) := rfl

end
end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutProjectionGeometry

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}

theorem squarePullback_eq_cast
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hs : slots = projected)
    (hk : ∀ s k, HEq (q s k) (MixedSupport.Projection.keep (slots s k)))
    (f : squareSpace (H projected)) :
    ChildBlockProjection.squarePullback q f = cast (congrArg
      (fun ss : Slots branch n → Fin t → MixedSupport.Slot =>
        (squareSpace (H ss) : Type)) hs.symm) f := by
  cases hs
  have hq : q = fun s k => MixedSupport.Projection.keep (slots s k) := by
    funext s k
    exact eq_of_heq (hk s k)
  subst q
  apply Subtype.ext
  rfl

theorem arraysPullback_eq_cast (rows : Nat → Nat)
    (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (hs : slots = projected)
    (hk : ∀ s k, HEq (q s k) (MixedSupport.Projection.keep (slots s k)))
    (arrays : Arrays projected rows) :
    ChildBlockProjection.arraysPullback rows q arrays = cast (congrArg
      (fun ss : Slots branch n → Fin t → MixedSupport.Slot => Arrays ss rows) hs.symm) arrays := by
  cases hs
  have hq : q = fun s k => MixedSupport.Projection.keep (slots s k) := by
    funext s k
    exact eq_of_heq (hk s k)
  subst q
  funext node row
  apply Subtype.ext
  rfl

end
end PerfectCompleteness.CutProjectionGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerReplayGroupingTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutSamplerReplayGroupingTransport

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls CutSamplerKeyLocality
open scoped Classical

noncomputable section

universe u v

theorem cast_pi_apply {I : Type u} {A B : I → Type v}
    (h : ((i : I) → A i) = ((i : I) → B i)) (hA : ∀ i, A i = B i)
    (f : (i : I) → A i) (i : I) :
    (cast h f) i = cast (hA i) (f i) := by
  have hAB : A = B := funext hA
  cases hAB
  rfl

end
end PerfectCompleteness.CutSamplerReplayGroupingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutGroupedProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalScalarProjection

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluate_tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (tape : RecursiveSampler.Tape F2 repeats p (LeafDomain right)) (x : Domain left),
      (RecursiveSampler.evaluate F2 repeats p (LeafDomain left)
        (tapePullback repeats p left right q tape)).val x =
      (RecursiveSampler.evaluate F2 repeats p (LeafDomain right) tape).val
        (sourceProjection q x) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q tape x
          rfl
      | step i p =>
          intro left right q tape x
          simp only [RecursiveSampler.evaluate_step, RecursiveSampler.combine,
            RecursiveSampler.combineFunction, Finset.sum_apply, Pi.add_apply, Pi.mul_apply,
            PointwiseSpaces.pullback_apply]
          change
            (∑ j : OffPath i,
              (ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection q j.val)
                (tape (.inl j))).val (restrictChild left j.val x)) +
              (∑ h : Fin (repeats (n + 1)),
                (RecursiveSampler.evaluate F2 repeats p (LeafDomain (childSlots left i))
                  (tapePullback repeats p (childSlots left i) (childSlots right i)
                    (ChildAssemblyProjection.childProjection q i)
                    (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h false))).val
                      (restrictChild left i x) *
                (RecursiveSampler.evaluate F2 repeats p (LeafDomain (childSlots left i))
                  (tapePullback repeats p (childSlots left i) (childSlots right i)
                    (ChildAssemblyProjection.childProjection q i)
                    (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h true))).val
                      (restrictChild left i x)) =
            (∑ j : OffPath i, (tape (.inl j)).val (restrictChild right j.val (sourceProjection q x))) +
              (∑ h : Fin (repeats (n + 1)),
                (RecursiveSampler.evaluate F2 repeats p (LeafDomain (childSlots right i))
                  (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h false)).val
                    (restrictChild right i (sourceProjection q x)) *
                (RecursiveSampler.evaluate F2 repeats p (LeafDomain (childSlots right i))
                  (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h true)).val
                    (restrictChild right i (sourceProjection q x)))
          apply congrArg₂ (fun a b : F2 => a + b)
          · exact Finset.sum_congr rfl (fun _ _ => rfl)
          · apply Finset.sum_congr rfl
            intro h _
            apply congrArg₂ (fun a b : F2 => a * b)
            · exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h false)
                (restrictChild left i x)
            · exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (RecursiveSampler.subTape F2 repeats i p (LeafDomain right) tape h true)
                (restrictChild left i x)

theorem terminalFactor_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (call : TerminalIndex repeats p)
      (x : RecursiveSampler.DrawSpace F2 repeats p (LeafDomain right)
        (drawIndex repeats p call)),
      TerminalCalls.terminalSpaceEquiv F2 repeats p (LeafDomain left) call
          (factorPullback repeats p left right q (drawIndex repeats p call) x) =
        HPullback (CutGroupedProjection.cutProjection p q)
          (TerminalCalls.terminalSpaceEquiv F2 repeats p (LeafDomain right) call x) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q call x
          cases call
          rfl
      | step i p =>
          intro left right q call x
          exact ih p (childSlots left i) (childSlots right i)
            (ChildAssemblyProjection.childProjection q i) call.2 x

theorem exteriorFactor_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
      (_hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k)))
      (j : DrawIndex repeats p) (hj : ¬ IsTerminal repeats p j)
      (x : RecursiveSampler.DrawSpace F2 repeats p (LeafDomain right) j),
      factorPullback repeats p left right q j x =
        cast (factor_eq repeats p right left
          (fun s h => (hs s h).symm) j hj) x := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q hs hk j hj x
          exact False.elim (hj True.intro)
      | step i p =>
          intro left right q hs hk j hj x
          cases j with
          | inl j =>
              exact CutProjectionGeometry.squarePullback_eq_cast
                (childSlots left j.val) (childSlots right j.val)
                (ChildAssemblyProjection.childProjection q j.val)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs j)
                (fun s k => hk (j.val, s) (WholeCutExteriorTransport.outside_ordinary i p j s) k) x
          | inr j =>
              exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
                (fun s h k => hk (i, s) (WholeCutExteriorTransport.outside_selected i p s h) k)
                j.2 hj x

theorem prefixSplit_tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (tape : RecursiveSampler.Tape F2 repeats p (LeafDomain right)) :
    OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain left)
        (tapePullback repeats p left right q tape) =
      (terminalPullback repeats p q (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain right) tape).1,
        cast (scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm))
          (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain right) tape).2) := by
  apply Prod.ext
  · funext call
    exact terminalFactor_pullback repeats p left right q call (tape (drawIndex repeats p call))
  · funext j
    exact (exteriorFactor_pullback repeats p left right q hs hk j.val j.property (tape j.val)).trans
      (CutSamplerReplayGroupingTransport.cast_pi_apply
        (scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm))
        (fun j => factor_eq repeats p right left
          (fun s h => (hs s h).symm) j.val j.property)
        (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain right) tape).2 j).symm

theorem reconstruct_pullback_apply (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (values : OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain right))
    (exterior : OriginalTerminalSplit.ExteriorTape F2 repeats p (LeafDomain right))
    (x : Domain left) :
    (OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain left)
      (fun call => HPullback (CutGroupedProjection.cutProjection p q) (values call))
      (cast (scalarExterior_eq repeats p right left
        (fun s h => (hs s h).symm)) exterior)).val x =
      (OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain right)
        values exterior).val (sourceProjection q x) := by
  let tape := (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain right)).symm
    (values, exterior)
  have hsplit :
      OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain left)
          (tapePullback repeats p left right q tape) =
        (terminalPullback repeats p q values,
          cast (scalarExterior_eq repeats p right left
            (fun s h => (hs s h).symm)) exterior) := by
    simpa only [tape, Equiv.apply_symm_apply] using
      prefixSplit_tapePullback repeats p left right q hs hk tape
  have hleft := congrArg
    (OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain left)).symm hsplit
  simp only [Equiv.symm_apply_apply] at hleft
  unfold OriginalScalarReconstruction.reconstruct
  change (RecursiveSampler.evaluate F2 repeats p (LeafDomain left)
    ((OriginalScalarReconstruction.prefixSplit F2 repeats p (LeafDomain left)).symm
      (terminalPullback repeats p q values,
        cast (scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm)) exterior))).val x =
    (RecursiveSampler.evaluate F2 repeats p (LeafDomain right) tape).val (sourceProjection q x)
  rw [← hleft]
  exact evaluate_tapePullback repeats p left right q tape x

theorem reconstruct_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (values : OriginalScalarReconstruction.TerminalValues F2 repeats p (LeafDomain right))
    (exterior : OriginalTerminalSplit.ExteriorTape F2 repeats p (LeafDomain right)) :
    OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain left)
      (fun call => HPullback (CutGroupedProjection.cutProjection p q) (values call))
      (cast (scalarExterior_eq repeats p right left
        (fun s h => (hs s h).symm)) exterior) =
      HPullback q (OriginalScalarReconstruction.reconstruct F2 repeats p (LeafDomain right)
        values exterior) := by
  apply Subtype.ext
  funext x
  exact reconstruct_pullback_apply repeats p left right q hs hk values exterior x

end
end PerfectCompleteness.OriginalScalarProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_OriginalWholeCutProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OriginalWholeCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape OriginalWholeCut
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

private theorem cast_exterior_parts {I J A A' B B' : Type} {C C' : J → Type}
    (ha : A = A') (hb : B = B') (hc : ∀ j, C j = C' j)
    (h : ((I → A) × (B × ((j : J) → C j))) = ((I → A') × (B' × ((j : J) → C' j))))
    (x : (I → A) × (B × ((j : J) → C j))) :
    cast h x = (fun i => cast ha (x.1 i), (cast hb x.2.1, fun j => cast (hc j) (x.2.2 j))) := by
  have hC : C = C' := funext hc
  cases ha
  cases hb
  cases hC
  rfl

theorem exteriorEquiv_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (left right : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (.step i p) s → left s = right s)
    (ext : Exterior rows repeats (.step i p) right) :
    exteriorEquiv rows repeats (.step i p) right left (fun s h => (hs s h).symm) ext =
      (fun bucket => cast
        (OriginalScalarProjection.scalarExterior_eq repeats (.step i p) right left
          (fun s h => (hs s h).symm)) (ext.1 bucket),
        (exteriorEquiv rows repeats p (childSlots right i) (childSlots left i)
          (fun s h => (hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h)).symm) ext.2.1,
          fun j => cast (congrArg (fun ss => Arrays ss rows)
            (WholeCutExteriorTransport.ordinarySlots_eq i p right left
              (fun s h => (hs s h).symm) j)) (ext.2.2 j))) :=
  cast_exterior_parts _ _ _ _ ext

private theorem reconstruct_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : Exterior rows repeats (.step i p) slots)
    (values : Values rows repeats (.step i p) slots)
    (below : BelowArrays rows (.step i p) slots) :
    reconstruct rows repeats (.step i p) slots ext values below (.inl ()) =
      reconstructBuckets rows repeats (.step i p) slots
        (fun bucket terminal => values (.inl (bucket, terminal))) ext.1 := rfl

private theorem reconstruct_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : Exterior rows repeats (.step i p) slots)
    (values : Values rows repeats (.step i p) slots)
    (below : BelowArrays rows (.step i p) slots) (node : Nodes branch n) :
    reconstruct rows repeats (.step i p) slots ext values below (.inr (i, node)) =
      reconstruct rows repeats p (childSlots slots i) ext.2.1
        (fun call => values (.inr call)) below node := by
  exact congrFun (WholeArraySampler.childrenAt_selected slots rows i
    (reconstruct rows repeats p (childSlots slots i) ext.2.1
      (fun call => values (.inr call)) below) ext.2.2) node

private theorem reconstruct_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : Exterior rows repeats (.step i p) slots)
    (values : Values rows repeats (.step i p) slots)
    (below : BelowArrays rows (.step i p) slots)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    reconstruct rows repeats (.step i p) slots ext values below (.inr (j.val, node)) =
      ext.2.2 j node := by
  exact congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
    (reconstruct rows repeats p (childSlots slots i) ext.2.1
      (fun call => values (.inr call)) below) ext.2.2 j) node

private theorem bucket_evaluate_pullback {ΩL ΩR : Type*} (width : Nat)
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (evalL : ΩL → H left) (evalR : ΩR → H right)
    (tapeL : BucketSampler.Tape width ΩL) (tapeR : BucketSampler.Tape width ΩR)
    (heval : ∀ bucket x, (evalL (tapeL bucket)).val x =
      (evalR (tapeR bucket)).val (sourceProjection q x)) :
    BucketSampler.evaluate width evalL tapeL =
      fun row => HPullback q (BucketSampler.evaluate width evalR tapeR row) := by
  funext row
  apply Subtype.ext
  funext x
  exact (BucketSampler.evaluate_apply width (H left) evalL tapeL row x).trans
    ((Finset.sum_congr rfl (fun bucket _ =>
      congrArg (fun z : F2 => bucket.val row * z) (heval bucket x))).trans
        (BucketSampler.evaluate_apply width (H right) evalR tapeR row
          (sourceProjection q x)).symm)

theorem reconstruct_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
      (_ : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k)))
      (ext : Exterior rows repeats p right) (values : Values rows repeats p right)
      (below : BelowArrays rows p right),
    reconstruct rows repeats p left
        (exteriorEquiv rows repeats p right left (fun s h => (hs s h).symm) ext)
        (fun call => HPullback (CutGroupedProjection.cutProjection p q) (values call))
        (fun child => ChildBlockProjection.arraysPullback rows
          (ChildAssemblyProjection.childProjection (CutGroupedProjection.cutProjection p q) child)
          (below child)) =
      ChildBlockProjection.arraysPullback rows q (reconstruct rows repeats p right ext values below) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q hs hk ext values below
          funext node row
          rcases node with u | ⟨child, node⟩
          · cases u
            change BucketSampler.evaluate (rows (n + 1)) id
                (fun a => HPullback q (values a)) row =
              HPullback q (BucketSampler.evaluate (rows (n + 1)) id values row)
            simp only [BucketSampler.evaluate, id_eq, map_sum, map_smul]
            rfl
          · rfl
      | step i p =>
          intro left right q hs hk ext values below
          let leftValues : Values rows repeats (.step i p) left :=
            fun call => HPullback (CutGroupedProjection.cutProjection (.step i p) q) (values call)
          let leftBelow : BelowArrays rows (.step i p) left :=
            fun child => ChildBlockProjection.arraysPullback rows
              (ChildAssemblyProjection.childProjection (CutGroupedProjection.cutProjection (.step i p) q) child)
              (below child)
          let leftExterior : Exterior rows repeats (.step i p) left :=
            (fun bucket => cast
              (OriginalScalarProjection.scalarExterior_eq repeats (.step i p) right left
                (fun s h => (hs s h).symm)) (ext.1 bucket),
              (exteriorEquiv rows repeats p (childSlots right i) (childSlots left i)
                (fun s h => (hs (i, s)
                  (WholeCutExteriorTransport.outside_selected i p s h)).symm) ext.2.1,
                fun j => cast (congrArg (fun ss => Arrays ss rows)
                  (WholeCutExteriorTransport.ordinarySlots_eq i p right left
                    (fun s h => (hs s h).symm) j)) (ext.2.2 j)))
          have hext : exteriorEquiv rows repeats (.step i p) right left
              (fun s h => (hs s h).symm) ext = leftExterior :=
            exteriorEquiv_step rows repeats i p left right hs ext
          refine (congrArg (fun e : Exterior rows repeats (.step i p) left =>
            reconstruct rows repeats (.step i p) left e leftValues leftBelow) hext).trans ?_
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            have hrootL := reconstruct_root rows repeats i p left leftExterior leftValues leftBelow
            have hrootR := reconstruct_root rows repeats i p right ext values below
            have hbucket := bucket_evaluate_pullback (rows (n + 1)) left right q
              (id : H left → H left) (id : H right → H right)
              (fun bucket => OriginalScalarReconstruction.reconstruct F2 repeats (.step i p)
                (LeafDomain left) (fun terminal => leftValues (.inl (bucket, terminal)))
                (leftExterior.1 bucket))
              (fun bucket => OriginalScalarReconstruction.reconstruct F2 repeats (.step i p)
                (LeafDomain right) (fun terminal => values (.inl (bucket, terminal))) (ext.1 bucket))
              (fun bucket x => OriginalScalarProjection.reconstruct_pullback_apply repeats (.step i p)
                left right q hs hk
                (fun terminal => values (.inl (bucket, terminal))) (ext.1 bucket) x)
            exact congrFun (hrootL.trans (hbucket.trans
              (congrArg (fun f : Fin (rows (n + 1)) → H right =>
                fun r => HPullback q (f r)) hrootR).symm)) row
          · by_cases hji : j = i
            · subst j
              have hnodeL := congrFun
                (reconstruct_selected rows repeats i p left leftExterior leftValues leftBelow node) row
              have hnodeR := congrFun
                (reconstruct_selected rows repeats i p right ext values below node) row
              have hchild := congrFun (congrFun
                (ih p (childSlots left i) (childSlots right i) (fun s k => q (i, s) k)
                  (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
                  (fun s h k => hk (i, s) (WholeCutExteriorTransport.outside_selected i p s h) k)
                  ext.2.1 (fun call => values (.inr call)) below) node) row
              exact hnodeL.trans (hchild.trans
                (congrArg (HPullback (ChildBlockProjection.nodeProjection q (.inr (i, node))))
                  hnodeR).symm)
            · have hnodeL := congrFun
                (reconstruct_ordinary rows repeats i p left leftExterior leftValues leftBelow ⟨j, hji⟩ node) row
              have hnodeR := congrFun
                (reconstruct_ordinary rows repeats i p right ext values below ⟨j, hji⟩ node) row
              have hcast := CutProjectionGeometry.arraysPullback_eq_cast rows
                (childSlots left j) (childSlots right j) (fun s k => q (j, s) k)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs ⟨j, hji⟩)
                (fun s k => hk (j, s) (WholeCutExteriorTransport.outside_ordinary i p ⟨j, hji⟩ s) k)
                (ext.2.2 ⟨j, hji⟩)
              have hcastRow := congrFun (congrFun hcast.symm node) row
              exact hnodeL.trans (hcastRow.trans
                (congrArg (HPullback (ChildBlockProjection.nodeProjection q (.inr (j, node))))
                  hnodeR).symm)

end
end PerfectCompleteness.OriginalWholeCutProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_SelectedArrayProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SelectedArrayProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArraySubtreeSplit SelectedArrayReplacement
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

private theorem replace_selected (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (arrays : Arrays slots rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots (.step i p) slots))
    (node : Nodes branch n) :
    replace rows (.step i p) slots arrays fresh (.inr (i, node)) =
      replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh node :=
  congrFun (WholeArraySampler.childrenAt_selected slots rows i
    (replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh)
    (fun child v => arrays (.inr (child.val, v)))) node

private theorem replace_ordinary (rows : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (arrays : Arrays slots rows)
    (fresh : Fin (rows (m + 1)) → H (subtreeSlots (.step i p) slots))
    (child : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    replace rows (.step i p) slots arrays fresh (.inr (child.val, node)) =
      arrays (.inr (child.val, node)) :=
  congrFun (WholeArraySampler.childrenAt_ordinary slots rows i
    (replace rows p (childSlots slots i) (fun v => arrays (.inr (i, v))) fresh)
    (fun j v => arrays (.inr (j.val, v))) child) node

theorem replace_pullback (rows : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (arrays : Arrays right rows)
      (fresh : Fin (rows (m + 1)) → H (subtreeSlots p right)),
      replace rows p left (ChildBlockProjection.arraysPullback rows q arrays)
          (fun row => HPullback (CutGroupedProjection.cutProjection p q) (fresh row)) =
        ChildBlockProjection.arraysPullback rows q (replace rows p right arrays fresh) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q arrays fresh
          funext node row
          rcases node with u | ⟨child, node⟩
          · cases u
            rfl
          · rfl
      | step i p =>
          intro left right q arrays fresh
          funext node row
          rcases node with u | ⟨child, node⟩
          · cases u
            rfl
          · change replace rows (.step i p) left
                (ChildBlockProjection.arraysPullback rows q arrays)
                (fun row => HPullback (CutGroupedProjection.cutProjection (.step i p) q)
                  (fresh row)) (.inr (child, node)) row =
              HPullback (ChildBlockProjection.nodeProjection q (.inr (child, node)))
                (replace rows (.step i p) right arrays fresh (.inr (child, node)) row)
            by_cases hchild : child = i
            · subst child
              rw [replace_selected, replace_selected]
              exact congrFun (congrFun
                (ih p (childSlots left i) (childSlots right i)
                  (ChildAssemblyProjection.childProjection q i)
                  (fun node => arrays (.inr (i, node))) fresh) node) row
            · rw [replace_ordinary rows i p left _ _ ⟨child, hchild⟩ node,
                replace_ordinary rows i p right arrays fresh ⟨child, hchild⟩ node]
              rfl

end
end PerfectCompleteness.SelectedArrayProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_UpperScalarCutProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_fresh _root_.OAI.PerfectCompleteness.ExtraCutCall.splitRecord_oldCall _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.OriginalCutBucketLaw.oldRecord_numberRecord _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.assembleRecord_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.recordEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UpperScalarCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open OriginalWholeCutTape WholeArrayInteriorExterior
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n j i t : Nat}

theorem reconstruct_pullback (rows repeats : Nat → Nat) (p : Path branch n (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCut.Record rows repeats p right) :
    OriginalWholeCut.reconstructRecord rows repeats p left
        (oldRecordPullback rows repeats p left right q hs record) =
      ChildBlockProjection.arraysPullback rows q
        (OriginalWholeCut.reconstructRecord rows repeats p right record) :=
  OriginalWholeCutProjection.reconstruct_pullback rows repeats p left right q hs hk
    record.1 record.2.1 record.2.2

theorem rootBuckets_pullback (rows repeats : Nat → Nat)
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch (j + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside r s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside r s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCut.Record rows repeats r right) :
    UpperScalarCutBucket.rootBuckets rows repeats r left
        (oldRecordPullback rows repeats r left right q hs record) =
      fun a => HPullback q (UpperScalarCutBucket.rootBuckets rows repeats r right record a) := by
  cases r with
  | refl => rfl
  | step child r =>
      funext a
      unfold oldRecordPullback
      rw [OriginalWholeCutProjection.exteriorEquiv_step rows repeats child r left right hs record.1]
      exact OriginalScalarProjection.reconstruct_pullback repeats (.step child r)
        left right q hs hk (fun terminal => record.2.1 (.inl (a, terminal))) (record.1.1 a)

theorem upperBuckets_pullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1)) :
    ∀ (r : Path branch (j + 1) (i + 1))
      (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s),
      (∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k))) →
      ∀ (record : OriginalWholeCut.Record rows repeats (p.append r) right),
    UpperScalarCutBucket.upperBuckets rows repeats p r left
        (oldRecordPullback rows repeats (p.append r) left right q hs record) =
      fun a => HPullback (CutGroupedProjection.cutProjection p q)
        (UpperScalarCutBucket.upperBuckets rows repeats p r right record a) := by
  induction n generalizing j with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl =>
          intro r left right q hs hk record
          exact rootBuckets_pullback rows repeats r left right q hs hk record
      | step child p =>
          intro r left right q hs hk record
          unfold oldRecordPullback
          have hext := OriginalWholeCutProjection.exteriorEquiv_step rows repeats child
            (p.append r) left right hs record.1
          refine (congrArg (fun exterior : OriginalWholeCutTape.Exterior rows repeats
              ((Path.step child p).append r) left =>
            UpperScalarCutBucket.upperBuckets rows repeats (.step child p) r left
              (exterior, ChildAssemblyProjection.assembledPullback rows
                (CutGroupedProjection.cutProjection ((Path.step child p).append r) q)
                record.2)) hext).trans ?_
          exact ih p r (childSlots left child) (childSlots right child) (fun s k => q (child, s) k)
            (fun s h => hs (child, s) (WholeCutExteriorTransport.outside_selected child (p.append r) s h))
            (fun s h k => hk (child, s) (WholeCutExteriorTransport.outside_selected child (p.append r) s h) k)
            (record.1.2.1, (fun call => record.2.1 (.inr call), record.2.2))

theorem map_updated_buckets {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [Module F2 A] [Module F2 B] {w : Nat} (f : A →ₗ[F2] B)
    (buckets : BucketSampler.Tape w A) (a : BucketSampler.Direction w) (fresh : A) :
    BucketSampler.evaluate w id (Function.update (fun b => f (buckets b)) a (f fresh)) =
      fun row => f (BucketSampler.evaluate w id (Function.update buckets a fresh) row) := by
  have hupdate : Function.update (fun b => f (buckets b)) a (f fresh) =
      fun b => f (Function.update buckets a fresh b) := by
    funext b
    by_cases h : b = a <;> simp [h]
  rw [hupdate]
  funext row
  simp only [BucketSampler.evaluate, id_eq, map_sum, map_smul]

theorem replaceArrays_pullback (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCut.Record rows repeats (p.append r) right)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p right)) :
    UpperScalarCutBucket.replaceArrays rows repeats p r left
        (oldRecordPullback rows repeats (p.append r) left right q hs record) a
        (HPullback (CutGroupedProjection.cutProjection p q) fresh) =
      ChildBlockProjection.arraysPullback rows q
        (UpperScalarCutBucket.replaceArrays rows repeats p r right record a fresh) := by
  unfold UpperScalarCutBucket.replaceArrays
  rw [reconstruct_pullback rows repeats (p.append r) left right q hs hk,
    upperBuckets_pullback rows repeats p r left right q hs hk,
    map_updated_buckets]
  exact SelectedArrayProjection.replace_pullback rows p left right q _ _

theorem pairRecord_pullback_oai (rows repeats : Nat → Nat) (p : Path branch n (j + 1))
    (r : Path branch (j + 1) (i + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → left s = right s)
    (hk : ∀ s, WholeCutExteriorTransport.Outside (p.append r) s → ∀ k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (record : OriginalWholeCut.Record rows repeats (p.append r) right)
    (a : BucketSampler.Direction (rows (j + 1))) (fresh : H (cutSlots p right)) :
    UpperScalarCutBucket.pairRecord rows repeats p r left
        (oldRecordPullback rows repeats (p.append r) left right q hs record) a
        (HPullback (CutGroupedProjection.cutProjection p q) fresh) =
      projectedPair rows p left right q
        (OriginalWholeCut.reconstructRecord rows repeats (p.append r) right record)
        (UpperScalarCutBucket.upperBuckets rows repeats p r right record) a fresh := by
  unfold UpperScalarCutBucket.pairRecord projectedPair
  rw [reconstruct_pullback rows repeats (p.append r) left right q hs hk,
    replaceArrays_pullback rows repeats p r left right q hs hk]
  rfl

attribute [local instance] linearMapFintype

end
end PerfectCompleteness.UpperScalarCutProjection

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.UpperScalarCutProjection.pairRecord_pullback_oai := @OAI.PerfectCompleteness.UpperScalarCutProjection.pairRecord_pullback_oai
