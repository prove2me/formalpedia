-- Prove2me | solution 1 for OAI.PerfectCompleteness.SourceQuestionPhysicalCollision.rawEvent_observe
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:20:48.465048+00:00
-- url     : https://prove2.me/submissions/35889896-70d4-4ec7-ae34-4b5ed9a210c1

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
import Definitions.Def_OAIQ252P017

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ChildAssemblyProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ChildAssemblyProjection

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}

theorem recursiveSum_pullback
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (f : (i : Fin (branch n)) → squareSpace (H (childSlots projected i))) :
    UniformChildSum.recursiveSum (LeafDomain slots)
        (fun i => ChildBlockProjection.squarePullback (childProjection p i) (f i)) =
      HPullback p (UniformChildSum.recursiveSum (LeafDomain projected) f) := by
  apply Subtype.ext
  change (∑ i, PointwiseSpaces.pullback F2 (childRestriction (LeafDomain slots) i)
      (ChildBlockProjection.squarePullback (childProjection p i) (f i)).val) =
    PointwiseSpaces.pullback F2 (sourceProjection p)
      (∑ i, PointwiseSpaces.pullback F2 (childRestriction (LeafDomain projected) i) (f i).val)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

variable {C : Type*} [Fintype C]

omit [Fintype C] in
theorem assemble_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (block : CutChildGrouping.Raw (C := C) projected rows) :
    CutChildGrouping.assemble slots rows (rawPullback rows p block) =
      assembledPullback rows p (CutChildGrouping.assemble projected rows block) := by
  apply Prod.ext
  · funext call
    exact recursiveSum_pullback p (fun i => (block i).1 call)
  · rfl

end
end PerfectCompleteness.ChildAssemblyProjection

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerDirectionFiber
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

end
end PerfectCompleteness.LowerDirectionFiber

end

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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
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

end
end PerfectCompleteness.LowerCutNodeCoordinates

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutRowsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutRows

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem selectedRows_evaluate_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (tape : WholeCutSampler.Tape rows repeats (.step i p) slots) :
    SelectedArrayReplacement.selectedRows rows (.step i p) slots
        (WholeCutSampler.evaluate rows repeats (.step i p) slots tape) =
      SelectedArrayReplacement.selectedRows rows p (childSlots slots i)
        (WholeCutSampler.evaluate rows repeats p (childSlots slots i) tape.2.1) := by
  rw [SelectedArrayReplacement.selectedRows_step]
  apply congrArg (SelectedArrayReplacement.selectedRows rows p (childSlots slots i))
  funext node
  unfold WholeCutSampler.evaluate
  rw [WholeArraySampler.evaluate_selected]
  rfl

theorem selectedRows_evaluate (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (tape : WholeCutSampler.Tape rows repeats p slots) (row : Fin (rows (m + 1))),
      SelectedArrayReplacement.selectedRows rows p slots
          (WholeCutSampler.evaluate rows repeats p slots tape) row =
        (CutChildGrouping.assemble (cutSlots p slots) rows
          ((splitTape rows repeats p slots tape).2)).1
            (WholeCutCalls.directRow rows repeats p row) := by
  induction n generalizing m with
  | zero => cases p
  | succ n ih =>
      cases p with
      | refl => intro slots tape row; rfl
      | step i p =>
          intro slots tape row
          rw [selectedRows_evaluate_step]
          exact ih p (childSlots slots i) tape.2.1 row

theorem selectedRows_reconstruct (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) (row : Fin (rows (m + 1))) :
    SelectedArrayReplacement.selectedRows rows p slots
        (reconstruct rows repeats p slots exterior raw) row =
      (CutChildGrouping.assemble (cutSlots p slots) rows raw).1
        (WholeCutCalls.directRow rows repeats p row) := by
  unfold reconstruct
  rw [selectedRows_evaluate, Equiv.apply_symm_apply]

theorem selectedRows_reconstruct_eq (rows repeats : Nat → Nat)
    (p : Path branch n (m + 1))
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (exterior : Exterior rows repeats p slots)
    (raw : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (cutSlots p slots) rows) :
    SelectedArrayReplacement.selectedRows rows p slots
        (reconstruct rows repeats p slots exterior raw) =
      selectRows rows repeats p slots
        (CutChildGrouping.assemble (cutSlots p slots) rows raw) := by
  funext row
  exact selectedRows_reconstruct rows repeats p slots exterior raw row

end
end PerfectCompleteness.LowerCutRows

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

namespace PerfectCompleteness.LowerCutPair

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
  (slots : Slots branch n → Fin t → MixedSupport.Slot)

theorem second_outside (exterior : Exterior rows repeats p slots)
    (a : BucketSampler.Direction (rows (m + 1))) (raw : Raw rows repeats p slots)
    (node : Nodes branch n) (hne : node ≠ WholeArrayInteriorExterior.upperNode p) :
    second rows repeats p slots exterior a raw node =
      first rows repeats p slots exterior raw node :=
  SelectedArrayReplacement.replace_outside rows p slots _ _ node hne

end
end PerfectCompleteness.LowerCutPair

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutPairBackground
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_otherCall _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_ownBucket _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.indexEquiv_symm_inl _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_own _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_other _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.valuesEquiv_symm_own _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.squareProduct_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalSourceSwap.outside_join _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.restrict_join _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedPathHead.child_step _root_.OAI.PerfectCompleteness.StoppedPathHead.tail_step _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
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

@[simp] theorem observe_rows (exterior : Exterior rows repeats p slots)
    (raw : LowerCutPair.Raw rows repeats p slots) :
    (observe rows repeats p slots raw).2.1 =
      SelectedArrayReplacement.selectedRows rows p slots
        (LowerCutPair.first rows repeats p slots exterior raw) := by
  exact (LowerCutRows.selectedRows_reconstruct_eq rows repeats p slots exterior _).symm

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

end
end PerfectCompleteness.LowerCutPairBackground

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerCutFiberDisintegrationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerCutProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

noncomputable section

section Linear

variable {H K : Type*} [AddCommGroup H] [AddCommGroup K]
  [Module F2 H] [Module F2 K] {ℓ : Nat}

theorem linearMap_replace (f : H →ₗ[F2] K) (a : BucketSampler.Direction ℓ)
    (S : Fin ℓ → H) (fresh : H) :
    (fun i => f (LowerDirectionFiber.replace a S fresh i)) =
      LowerDirectionFiber.replace a (fun i => f (S i)) (f fresh) := by
  rw [LowerDirectionFiber.replace_eq, LowerDirectionFiber.replace_eq]
  funext i
  simp only [Pi.add_apply, BucketSampler.rankOne, map_add, map_smul, map_sub]

end Linear

section Local

variable {branch : Nat → Nat} {n t : Nat} {C : Type*} [Fintype C]
  {slots projected : Slots branch (n + 1) → Fin t → MixedSupport.Slot}

omit [Fintype C] in
theorem original_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (raw : CutCallExtension.Extended (C := C) projected rows) :
    CutCallExtension.original slots rows
        (ChildAssemblyProjection.rawPullback (C := Option C) rows p raw) =
      ChildAssemblyProjection.rawPullback (C := C) rows p
        (CutCallExtension.original projected rows raw) := rfl

omit [Fintype C] in
theorem fresh_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (raw : CutCallExtension.Extended (C := C) projected rows) :
    CutCallExtension.fresh slots rows
        (ChildAssemblyProjection.rawPullback (C := Option C) rows p raw) =
      HPullback p (CutCallExtension.fresh projected rows raw) :=
  ChildAssemblyProjection.recursiveSum_pullback p (fun i => (raw i).1 none)

theorem HPullback_replace {ℓ : Nat}
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (a : BucketSampler.Direction ℓ) (S : Fin ℓ → H projected) (fresh : H projected) :
    (fun i => HPullback p (LowerDirectionFiber.replace a S fresh i)) =
      LowerDirectionFiber.replace a (fun i => HPullback p (S i)) (HPullback p fresh) :=
  linearMap_replace (HPullback p) a S fresh

end Local

section Selected

variable {branch : Nat → Nat} {n m t : Nat}
  (rows repeats : Nat → Nat) (path : Path branch n (m + 1))
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

theorem firstRows_pullback
    (p : ∀ s k, MixedSupport.Projection
      (WholeCutGrouping.cutSlots path slots s k) (WholeCutGrouping.cutSlots path projected s k))
    (exterior : WholeCutGrouping.Exterior rows repeats path slots)
    (projectedExterior : WholeCutGrouping.Exterior rows repeats path projected)
    (raw : LowerCutPair.Raw rows repeats path projected) :
    SelectedArrayReplacement.selectedRows rows path slots
        (LowerCutPair.first rows repeats path slots exterior
          (ChildAssemblyProjection.rawPullback rows p raw)) =
      (fun i => HPullback p
        (SelectedArrayReplacement.selectedRows rows path projected
          (LowerCutPair.first rows repeats path projected projectedExterior raw) i)) := by
  simp only [LowerCutPair.first, LowerCutRows.selectedRows_reconstruct_eq]
  rw [original_pullback]
  exact congrArg (LowerCutRows.selectRows rows repeats path slots)
    (ChildAssemblyProjection.assemble_pullback rows p
      (CutCallExtension.original (WholeCutGrouping.cutSlots path projected) rows raw))

theorem selectedPair_pullback
    (p : ∀ s k, MixedSupport.Projection
      (WholeCutGrouping.cutSlots path slots s k) (WholeCutGrouping.cutSlots path projected s k))
    (exterior : WholeCutGrouping.Exterior rows repeats path slots)
    (projectedExterior : WholeCutGrouping.Exterior rows repeats path projected)
    (a : BucketSampler.Direction (rows (m + 1)))
    (raw : LowerCutPair.Raw rows repeats path projected) :
    LowerCutPair.selectedPair rows repeats path slots exterior a
        (ChildAssemblyProjection.rawPullback rows p raw) =
      ((fun i => HPullback p
          ((LowerCutPair.selectedPair rows repeats path projected projectedExterior a raw).1 i)),
       (fun i => HPullback p
          ((LowerCutPair.selectedPair rows repeats path projected projectedExterior a raw).2 i))) := by
  simp only [LowerCutPair.selectedPair, LowerCutPair.selected_second]
  apply Prod.ext
  · exact firstRows_pullback rows repeats path p exterior projectedExterior raw
  · rw [firstRows_pullback rows repeats path p exterior projectedExterior raw]
    simp only [LowerCutPair.fresh]
    rw [fresh_pullback]
    exact (HPullback_replace p a _ _).symm

end Selected
end
end PerfectCompleteness.LowerCutProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

theorem childPullback_heq {C : Type*} [Fintype C] (rows : Nat → Nat)
    {left right left' right' : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (hL : left = left') (hR : right = right')
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (q' : ∀ s k, MixedSupport.Projection (left' s k) (right' s k))
    (hq : ∀ s k, HEq (q s k) (q' s k)) (i : Fin (branch n))
    (block : CutChildGrouping.Child (C := C) right rows i)
    (block' : CutChildGrouping.Child (C := C) right' rows i)
    (hb : HEq block block') :
    HEq (ChildAssemblyProjection.childPullback rows q i block)
      (ChildAssemblyProjection.childPullback rows q' i block') := by
  cases hL
  cases hR
  have hqq' : q = q' := by
    funext s k
    exact eq_of_heq (hq s k)
  cases hqq'
  have hbb' : block = block' := eq_of_heq hb
  cases hbb'
  rfl

private theorem keep_heq {a b : MixedSupport.Slot} (h : a = b) :
    HEq (MixedSupport.Projection.keep a) (MixedSupport.Projection.keep b) := by
  cases h
  rfl

theorem fillProjection_outside {m : Nat} (p : Path branch n m)
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch m → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (s : Slots branch n) (hout : s ∉ Set.range p.slotEmbedding) (k : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q s k)
      (MixedSupport.Projection.keep (CutSlotAssembly.fill p outside left s k)) := by
  revert outside left right q s hout k
  induction p with
  | refl _ =>
      intro outside left right q s hout k
      exact False.elim (hout ⟨s, rfl⟩)
  | step i p ih =>
      intro outside left right q s hout k
      obtain ⟨j, s⟩ := s
      by_cases hji : j = i
      · subst j
        have htail : s ∉ Set.range p.slotEmbedding := by
          rintro ⟨a, ha⟩
          exact hout ⟨a, congrArg (fun b => (i, b)) ha⟩
        have hfill : CutSlotAssembly.fill (.step i p) outside left (i, s) =
            CutSlotAssembly.fill p (fun b => outside (i, b)) left s :=
          ite_eq_left (show i = i from rfl)
        simp only [CutProjectionAssembly.fillProjection]
        exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
          ((ih (fun b => outside (i, b)) left right q s htail k).trans
            (keep_heq (congrFun hfill k).symm))
      · have hfill : CutSlotAssembly.fill (.step i p) outside left (j, s) = outside (j, s) :=
          ite_eq_right hji
        simp only [CutProjectionAssembly.fillProjection, dite_eq_right hji]
        exact (CutProjectionAssembly.castProjection_heq _ _ _).trans
          (keep_heq (congrFun hfill k).symm)

end
end PerfectCompleteness.CutProjectionGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutGroupedProjectionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CutGroupedProjection

open PointwiseSpaces RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open RecursiveSampler TerminalCalls
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluate_tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (tape : CutSamplerRefinement.Tape F2 repeats p (LeafDomain right)) (x : Domain left),
      (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain left)
        (tapePullback repeats p left right q tape)).val x =
      (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain right) tape).val
        (sourceProjection q x) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q tape x
          exact congrArg (fun f : H left => f.val x)
            (ChildAssemblyProjection.recursiveSum_pullback q (tape ()))
      | step i p =>
          intro left right q tape x
          simp only [CutSamplerLocality.evaluate_step, RecursiveSampler.combine,
            RecursiveSampler.combineFunction, Finset.sum_apply, Pi.add_apply, Pi.mul_apply,
            PointwiseSpaces.pullback_apply]
          change
            (∑ j : OffPath i,
              (ChildBlockProjection.squarePullback (ChildAssemblyProjection.childProjection q j.val)
                (tape (.inl j))).val (restrictChild left j.val x)) +
              (∑ h : Fin (repeats (n + 1)),
                (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain (childSlots left i))
                  (tapePullback repeats p (childSlots left i) (childSlots right i)
                    (ChildAssemblyProjection.childProjection q i)
                    (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h false))).val
                      (restrictChild left i x) *
                (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain (childSlots left i))
                  (tapePullback repeats p (childSlots left i) (childSlots right i)
                    (ChildAssemblyProjection.childProjection q i)
                    (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h true))).val
                      (restrictChild left i x)) =
            (∑ j : OffPath i, (tape (.inl j)).val (restrictChild right j.val (sourceProjection q x))) +
              (∑ h : Fin (repeats (n + 1)),
                (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain (childSlots right i))
                  (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h false)).val
                    (restrictChild right i (sourceProjection q x)) *
                (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain (childSlots right i))
                  (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h true)).val
                    (restrictChild right i (sourceProjection q x)))
          apply congrArg₂ (fun a b : F2 => a + b)
          · exact Finset.sum_congr rfl (fun _ _ => rfl)
          · apply Finset.sum_congr rfl
            intro h _
            apply congrArg₂ (fun a b : F2 => a * b)
            · exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h false)
                (restrictChild left i x)
            · exact ih p (childSlots left i) (childSlots right i)
                (ChildAssemblyProjection.childProjection q i)
                (CutSamplerLocality.subTape F2 repeats i p (LeafDomain right) tape h true)
                (restrictChild left i x)

theorem terminalFactor_pullback (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (call : TerminalIndex repeats p)
      (x : CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain right)
        (drawIndex repeats p call)),
      CutTerminalSplit.terminalFactorEquiv F2 repeats p (LeafDomain left) call
          (factorPullback repeats p left right q (drawIndex repeats p call) x) =
        fun child => ChildBlockProjection.squarePullback
          (ChildAssemblyProjection.childProjection (cutProjection p q) child)
          (CutTerminalSplit.terminalFactorEquiv F2 repeats p (LeafDomain right) call x child) := by
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
      (x : CutSamplerRefinement.RefinedSpace F2 repeats p (LeafDomain right) j),
      factorPullback repeats p left right q j x =
        cast (WholeCutExteriorTransport.factor_eq repeats p right left
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

theorem splitTape_tapePullback (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (tape : CutSamplerRefinement.Tape F2 repeats p (LeafDomain right)) :
    CutTerminalSplit.splitTape F2 repeats p (LeafDomain left)
        (tapePullback repeats p left right q tape) =
      (terminalPullback repeats p q (CutTerminalSplit.splitTape F2 repeats p (LeafDomain right) tape).1,
        cast (WholeCutExteriorTransport.scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm))
          (CutTerminalSplit.splitTape F2 repeats p (LeafDomain right) tape).2) := by
  apply Prod.ext
  · funext call
    exact terminalFactor_pullback repeats p left right q call (tape (drawIndex repeats p call))
  · funext j
    exact (exteriorFactor_pullback repeats p left right q hs hk j.val j.property (tape j.val)).trans
      (CutSamplerReplayGroupingTransport.cast_pi_apply
        (WholeCutExteriorTransport.scalarExterior_eq repeats p right left
          (fun s h => (hs s h).symm))
        (fun j => WholeCutExteriorTransport.factor_eq repeats p right left
          (fun s h => (hs s h).symm) j.val j.property)
        (CutTerminalSplit.splitTape F2 repeats p (LeafDomain right) tape).2 j).symm

theorem evaluate_rebuild (repeats : Nat → Nat) (p : Path branch n (m + 1))
    (left right : Slots branch n → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
    (hk : ∀ s (_hout : WholeCutExteriorTransport.Outside p s) k,
      HEq (q s k) (MixedSupport.Projection.keep (left s k)))
    (terminal : CutTerminalSplit.TerminalTape F2 repeats p (LeafDomain right))
    (exterior : CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain right)) (x : Domain left) :
    (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain left)
      ((CutTerminalSplit.splitTape F2 repeats p (LeafDomain left)).symm
        (terminalPullback repeats p q terminal,
          cast (WholeCutExteriorTransport.scalarExterior_eq repeats p right left
            (fun s h => (hs s h).symm)) exterior))).val x =
    (CutSamplerRefinement.evaluate F2 repeats p (LeafDomain right)
      ((CutTerminalSplit.splitTape F2 repeats p (LeafDomain right)).symm (terminal, exterior))).val
        (sourceProjection q x) := by
  let tape := (CutTerminalSplit.splitTape F2 repeats p (LeafDomain right)).symm (terminal, exterior)
  have hsplit :
      CutTerminalSplit.splitTape F2 repeats p (LeafDomain left)
          (tapePullback repeats p left right q tape) =
        (terminalPullback repeats p q terminal,
          cast (WholeCutExteriorTransport.scalarExterior_eq repeats p right left
            (fun s h => (hs s h).symm)) exterior) := by
    simpa only [tape, Equiv.apply_symm_apply] using
      splitTape_tapePullback repeats p left right q hs hk tape
  have hleft := congrArg (CutTerminalSplit.splitTape F2 repeats p (LeafDomain left)).symm hsplit
  simp only [Equiv.symm_apply_apply] at hleft
  rw [← hleft]
  exact evaluate_tapePullback repeats p left right q tape x

end
end PerfectCompleteness.CutGroupedProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_WholeCutGroupedProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutGroupedProjection

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem evaluateGrouped_root (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) slots)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats (.step i p))
      (WholeCutGrouping.cutSlots (.step i p) slots) rows) :
    evaluateGrouped rows repeats (.step i p) slots ext children (.inl ()) =
      BucketSampler.evaluate (rows (n + 1))
        (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain slots))
        (fun bucket => (CutTerminalSplit.splitTape F2 repeats (.step i p) (LeafDomain slots)).symm
          (fun terminal child => (children child).1 (.inl (bucket, terminal)), ext.1 bucket)) := rfl

theorem evaluateGrouped_selected (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) slots)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats (.step i p))
      (WholeCutGrouping.cutSlots (.step i p) slots) rows) (node : Nodes branch n) :
    evaluateGrouped rows repeats (.step i p) slots ext children (.inr (i, node)) =
      evaluateGrouped rows repeats p (childSlots slots i) ext.2.1
        (fun child => (fun call => (children child).1 (.inr call), (children child).2)) node :=
  WholeArraySampler.evaluate_selected rows repeats i p slots
    (WholeCutSampler.collapse rows repeats (.step i p) slots
      ((WholeCutGrouping.splitTape rows repeats (.step i p) slots).symm (ext, children))) node

theorem evaluateGrouped_ordinary (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) slots)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats (.step i p))
      (WholeCutGrouping.cutSlots (.step i p) slots) rows)
    (j : RecursiveSampler.OffPath i) (node : Nodes branch n) :
    evaluateGrouped rows repeats (.step i p) slots ext children (.inr (j.val, node)) =
      ext.2.2 j node :=
  WholeArraySampler.evaluate_ordinary rows repeats i p slots
    (WholeCutSampler.collapse rows repeats (.step i p) slots
      ((WholeCutGrouping.splitTape rows repeats (.step i p) slots).symm (ext, children))) j node

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

theorem exterior_equiv_step (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (left right : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (hs : ∀ s, WholeCutExteriorTransport.Outside (.step i p) s → left s = right s)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) right) :
    WholeCutExteriorTransport.equiv rows repeats (.step i p) right left
        (fun s h => (hs s h).symm) ext =
      (fun bucket => cast
        (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) right left
          (fun s h => (hs s h).symm)) (ext.1 bucket),
        (WholeCutExteriorTransport.equiv rows repeats p (childSlots right i) (childSlots left i)
          (fun s h => (hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h)).symm) ext.2.1,
          fun j => cast (congrArg (fun ss => Arrays ss rows)
            (WholeCutExteriorTransport.ordinarySlots_eq i p right left
              (fun s h => (hs s h).symm) j)) (ext.2.2 j))) :=
  cast_exterior_parts _ _ _ _ ext

private theorem assembleArrays_pullback (rows : Nat → Nat)
    (left right : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (data : CutChildGrouping.Assembled (C := Fin (rows (n + 1))) right rows) :
    WholeCutSampler.assembleArrays left rows (ChildAssemblyProjection.assembledPullback rows q data) =
      ChildBlockProjection.arraysPullback rows q (WholeCutSampler.assembleArrays right rows data) := by
  funext node row
  rcases node with u | ⟨i, node⟩ <;> rfl

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

theorem evaluateGrouped_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (left right : Slots branch n → Fin t → MixedSupport.Slot)
      (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
      (hs : ∀ s, WholeCutExteriorTransport.Outside p s → left s = right s)
      (_ : ∀ s, WholeCutExteriorTransport.Outside p s → ∀ k,
        HEq (q s k) (MixedSupport.Projection.keep (left s k)))
      (ext : WholeCutGrouping.Exterior rows repeats p right)
      (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
        (WholeCutGrouping.cutSlots p right) rows),
    evaluateGrouped rows repeats p left
        (WholeCutExteriorTransport.equiv rows repeats p right left (fun s h => (hs s h).symm) ext)
        (ChildAssemblyProjection.rawPullback rows (CutGroupedProjection.cutProjection p q) children) =
      ChildBlockProjection.arraysPullback rows q
        (evaluateGrouped rows repeats p right ext children) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro left right q hs hk ext children
          exact (congrArg (WholeCutSampler.assembleArrays left rows)
            (ChildAssemblyProjection.assemble_pullback (C := Fin (rows (n + 1)))
              rows q children)).trans
            (assembleArrays_pullback rows left right q
              (CutChildGrouping.assemble right rows children))
      | step i p =>
          intro left right q hs hk ext children
          let leftChildren := ChildAssemblyProjection.rawPullback rows
            (CutGroupedProjection.cutProjection (.step i p) q) children
          let leftExterior : WholeCutGrouping.Exterior rows repeats (.step i p) left :=
            (fun bucket => cast
              (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) right left
                (fun s h => (hs s h).symm)) (ext.1 bucket),
              (WholeCutExteriorTransport.equiv rows repeats p (childSlots right i) (childSlots left i)
                (fun s h => (hs (i, s)
                  (WholeCutExteriorTransport.outside_selected i p s h)).symm) ext.2.1,
                fun j => cast (congrArg (fun ss => Arrays ss rows)
                  (WholeCutExteriorTransport.ordinarySlots_eq i p right left
                    (fun s h => (hs s h).symm) j)) (ext.2.2 j)))
          have hext : WholeCutExteriorTransport.equiv rows repeats (.step i p) right left
              (fun s h => (hs s h).symm) ext = leftExterior :=
            exterior_equiv_step rows repeats i p left right hs ext
          refine (congrArg
            (fun e : WholeCutGrouping.Exterior rows repeats (.step i p) left =>
              evaluateGrouped rows repeats (.step i p) left e leftChildren) hext).trans ?_
          funext node row
          rcases node with u | ⟨j, node⟩
          · cases u
            have hrootL := evaluateGrouped_root rows repeats i p left leftExterior leftChildren
            have hrootR := evaluateGrouped_root rows repeats i p right ext children
            have hbucket := bucket_evaluate_pullback (rows (n + 1)) left right q
              (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain left))
              (CutSamplerRefinement.evaluate F2 repeats (.step i p) (LeafDomain right))
              (fun bucket =>
                (CutTerminalSplit.splitTape F2 repeats (.step i p) (LeafDomain left)).symm
                  (fun terminal child => (leftChildren child).1 (.inl (bucket, terminal)),
                    leftExterior.1 bucket))
              (fun bucket =>
                (CutTerminalSplit.splitTape F2 repeats (.step i p) (LeafDomain right)).symm
                  (fun terminal child => (children child).1 (.inl (bucket, terminal)), ext.1 bucket))
              (fun bucket x => CutGroupedProjection.evaluate_rebuild repeats (.step i p)
                left right q hs hk
                (fun terminal child => (children child).1 (.inl (bucket, terminal))) (ext.1 bucket) x)
            exact congrFun (hrootL.trans (hbucket.trans
              (congrArg (fun f : Fin (rows (n + 1)) → H right =>
                fun r => HPullback q (f r)) hrootR).symm)) row
          · by_cases hji : j = i
            · subst j
              have hnodeL := congrFun
                (evaluateGrouped_selected rows repeats i p left leftExterior leftChildren node) row
              have hnodeR := congrFun
                (evaluateGrouped_selected rows repeats i p right ext children node) row
              have hchild := congrFun (congrFun
                (ih p (childSlots left i) (childSlots right i) (fun s k => q (i, s) k)
                  (fun s h => hs (i, s) (WholeCutExteriorTransport.outside_selected i p s h))
                  (fun s h k => hk (i, s) (WholeCutExteriorTransport.outside_selected i p s h) k)
                  ext.2.1 (fun child => (fun call => (children child).1 (.inr call), (children child).2))) node) row
              exact hnodeL.trans (hchild.trans
                (congrArg (HPullback (ChildBlockProjection.nodeProjection q (.inr (i, node))))
                  hnodeR).symm)
            · have hnodeL := congrFun
                (evaluateGrouped_ordinary rows repeats i p left leftExterior leftChildren ⟨j, hji⟩ node) row
              have hnodeR := congrFun
                (evaluateGrouped_ordinary rows repeats i p right ext children ⟨j, hji⟩ node) row
              have hcast := CutProjectionGeometry.arraysPullback_eq_cast rows
                (childSlots left j) (childSlots right j) (fun s k => q (j, s) k)
                (WholeCutExteriorTransport.ordinarySlots_eq i p left right hs ⟨j, hji⟩)
                (fun s k => hk (j, s) (WholeCutExteriorTransport.outside_ordinary i p ⟨j, hji⟩ s) k)
                (ext.2.2 ⟨j, hji⟩)
              have hcastRow := congrFun (congrFun hcast.symm node) row
              exact hnodeL.trans (hcastRow.trans
                (congrArg (HPullback (ChildBlockProjection.nodeProjection q (.inr (j, node))))
                  hnodeR).symm)

theorem exteriorAt_pullback (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (placeholder left right : Slots branch (m + 1) → Fin t → MixedSupport.Slot)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder left external =
      WholeCutExteriorTransport.equiv rows repeats p
        (CutSlotAssembly.fill p outside right) (CutSlotAssembly.fill p outside left)
        (fun s h => (CutSlotAssembly.fill_outside_eq p outside left right s h).symm)
        (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external) := by
  apply eq_of_heq
  have hleft : HEq
      (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder left external) external :=
    cast_heq _ _
  have hright : HEq
      (CleanPhysicalReplay.exteriorAt rows repeats p outside placeholder right external) external :=
    cast_heq _ _
  exact hleft.trans ((cast_heq _ _).trans hright).symm

end
end PerfectCompleteness.WholeCutGroupedProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionPairPullback
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPairPullback

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeArrayInteriorExterior

variable {branch : Nat → Nat} {n height t : Nat}

theorem selectedRows_pullback (rows : Nat → Nat) :
    {n height : Nat} → (path : Path branch n (height + 1)) →
      (left right : Slots branch n → Fin t → MixedSupport.Slot) →
      (p : ∀ leaf j, MixedSupport.Projection (left leaf j) (right leaf j)) →
      (arrays : Arrays right rows) →
      SelectedArrayReplacement.selectedRows rows path left
          (ChildBlockProjection.arraysPullback rows p arrays) =
        (fun i => HPullback (CutGroupedProjection.cutProjection path p)
          (SelectedArrayReplacement.selectedRows rows path right arrays i))
  | _, _, .refl _, _, _, _, _ => rfl
  | _, _, .step child path, left, right, p, arrays =>
      selectedRows_pullback rows path (childSlots left child) (childSlots right child)
        (fun leaf j => p (child, leaf) j) (fun node => arrays (.inr (child, node)))

section Grouped

variable (rows repeats : Nat → Nat) (path : Path branch n (height + 1))
  (left right : Slots branch n → Fin t → MixedSupport.Slot)
  (p : ∀ leaf j, MixedSupport.Projection (left leaf j) (right leaf j))
  (hs : ∀ leaf, WholeCutExteriorTransport.Outside path leaf → left leaf = right leaf)
  (hk : ∀ leaf, WholeCutExteriorTransport.Outside path leaf → ∀ j,
    HEq (p leaf j) (MixedSupport.Projection.keep (left leaf j)))
  (exterior : WholeCutGrouping.Exterior rows repeats path right)

include hk in

theorem first_grouped_pullback (raw : LowerCutPair.Raw rows repeats path right) :
    ChildBlockProjection.arraysPullback rows p
        (LowerCutPair.first rows repeats path right exterior raw) =
      LowerCutPair.first rows repeats path left
        (WholeCutExteriorTransport.equiv rows repeats path right left
          (fun leaf h => (hs leaf h).symm) exterior)
        (ChildAssemblyProjection.rawPullback rows
          (CutGroupedProjection.cutProjection path p) raw) := by
  symm
  change WholeCutGroupedProjection.evaluateGrouped rows repeats path left _
      (CutCallExtension.original (WholeCutGrouping.cutSlots path left) rows
        (ChildAssemblyProjection.rawPullback rows
          (CutGroupedProjection.cutProjection path p) raw)) =
    ChildBlockProjection.arraysPullback rows p
      (WholeCutGroupedProjection.evaluateGrouped rows repeats path right exterior
        (CutCallExtension.original (WholeCutGrouping.cutSlots path right) rows raw))
  rw [LowerCutProjection.original_pullback]
  exact WholeCutGroupedProjection.evaluateGrouped_pullback rows repeats path
    left right p hs hk exterior _

include hk in

theorem second_grouped_pullback
    (direction : BucketSampler.Direction (rows (height + 1)))
    (raw : LowerCutPair.Raw rows repeats path right) :
    ChildBlockProjection.arraysPullback rows p
        (LowerCutPair.second rows repeats path right exterior direction raw) =
      LowerCutPair.second rows repeats path left
        (WholeCutExteriorTransport.equiv rows repeats path right left
          (fun leaf h => (hs leaf h).symm) exterior) direction
        (ChildAssemblyProjection.rawPullback rows
          (CutGroupedProjection.cutProjection path p) raw) := by
  let exterior' := WholeCutExteriorTransport.equiv rows repeats path right left
    (fun leaf h => (hs leaf h).symm) exterior
  have hselected :
      SelectedArrayReplacement.selectedRows rows path left
          (ChildBlockProjection.arraysPullback rows p
            (LowerCutPair.second rows repeats path right exterior direction raw)) =
        SelectedArrayReplacement.selectedRows rows path left
          (LowerCutPair.second rows repeats path left exterior' direction
            (ChildAssemblyProjection.rawPullback rows
              (CutGroupedProjection.cutProjection path p) raw)) := by
    rw [selectedRows_pullback]
    exact (congrArg Prod.snd
      (LowerCutProjection.selectedPair_pullback rows repeats path
        (CutGroupedProjection.cutProjection path p) exterior' exterior direction raw)).symm
  funext node
  by_cases hnode : node = upperNode path
  · subst node
    simpa only [LowerCutNodeCoordinates.rowEquiv_selectedRows] using
      congrArg (LowerCutNodeCoordinates.rowEquiv rows path left) hselected
  · funext row
    change HPullback (ChildBlockProjection.nodeProjection p node)
        (LowerCutPair.second rows repeats path right exterior direction raw node row) =
      LowerCutPair.second rows repeats path left exterior' direction
        (ChildAssemblyProjection.rawPullback rows
          (CutGroupedProjection.cutProjection path p) raw) node row
    rw [LowerCutPair.second_outside rows repeats path right exterior direction raw node hnode,
      LowerCutPair.second_outside rows repeats path left exterior' direction _ node hnode]
    exact congrFun (congrFun
      (first_grouped_pullback rows repeats path left right p hs hk exterior raw) node) row

end Grouped

section Filled

private theorem rawCast_child_heq {C : Type*} [Fintype C] (rows : Nat → Nat)
    {source target : Slots branch (height + 1) → Fin t → MixedSupport.Slot}
    (h : source = target) (raw : CutChildGrouping.Raw (C := C) source rows)
    (i : Fin (branch height)) :
    HEq ((SourceQuestionLowerForms.rawCast rows h raw) i) (raw i) := by
  cases h
  rfl

theorem rawAtCut_pullback (rows repeats : Nat → Nat)
    (path : Path branch n (height + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
    (p : ∀ leaf j, MixedSupport.Projection (left leaf j) (right leaf j))
    (raw : CutCallExtension.Extended
      (C := WholeCutCalls.Index rows repeats path) right rows) :
    rawAtCut rows repeats path outside left
        (ChildAssemblyProjection.rawPullback rows p raw) =
      ChildAssemblyProjection.rawPullback rows
        (CutGroupedProjection.cutProjection path
          (CutProjectionAssembly.fillProjection path outside left right p))
        (rawAtCut rows repeats path outside right raw) := by
  funext i
  apply eq_of_heq
  exact (rawCast_child_heq rows
      (CleanPhysicalReplay.cutSlots_fill path outside left).symm
      (ChildAssemblyProjection.rawPullback rows p raw) i).trans
    (CutProjectionGeometry.childPullback_heq rows
      (CleanPhysicalReplay.cutSlots_fill path outside left)
      (CleanPhysicalReplay.cutSlots_fill path outside right)
      (CutGroupedProjection.cutProjection path
        (CutProjectionAssembly.fillProjection path outside left right p)) p
      (CutProjectionAssembly.fillProjection_at_cut path outside left right p) i
      (rawAtCut rows repeats path outside right raw i) (raw i)
      (rawCast_child_heq rows
        (CleanPhysicalReplay.cutSlots_fill path outside right).symm raw i)).symm

variable (rows repeats : Nat → Nat) (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder left right : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (p : ∀ leaf j, MixedSupport.Projection (left leaf j) (right leaf j))
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)

theorem first_pullback
    (raw : CutCallExtension.Extended
      (C := WholeCutCalls.Index rows repeats path) right rows) :
    ChildBlockProjection.arraysPullback rows
        (CutProjectionAssembly.fillProjection path outside left right p)
        (LowerCutPair.first rows repeats path (CutSlotAssembly.fill path outside right)
          (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder right exterior)
          (rawAtCut rows repeats path outside right raw)) =
      LowerCutPair.first rows repeats path (CutSlotAssembly.fill path outside left)
        (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder left exterior)
        (rawAtCut rows repeats path outside left
          (ChildAssemblyProjection.rawPullback rows p raw)) := by
  rw [rawAtCut_pullback,
    WholeCutGroupedProjection.exteriorAt_pullback rows repeats path outside placeholder
      left right exterior]
  exact first_grouped_pullback rows repeats path
    (CutSlotAssembly.fill path outside left) (CutSlotAssembly.fill path outside right)
    (CutProjectionAssembly.fillProjection path outside left right p)
    (CutSlotAssembly.fill_outside_eq path outside left right)
    (CutProjectionGeometry.fillProjection_outside path outside left right p)
    (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder right exterior) _

theorem second_pullback
    (direction : BucketSampler.Direction (rows (height + 1)))
    (raw : CutCallExtension.Extended
      (C := WholeCutCalls.Index rows repeats path) right rows) :
    ChildBlockProjection.arraysPullback rows
        (CutProjectionAssembly.fillProjection path outside left right p)
        (LowerCutPair.second rows repeats path (CutSlotAssembly.fill path outside right)
          (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder right exterior)
          direction (rawAtCut rows repeats path outside right raw)) =
      LowerCutPair.second rows repeats path (CutSlotAssembly.fill path outside left)
        (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder left exterior)
        direction (rawAtCut rows repeats path outside left
          (ChildAssemblyProjection.rawPullback rows p raw)) := by
  rw [rawAtCut_pullback,
    WholeCutGroupedProjection.exteriorAt_pullback rows repeats path outside placeholder
      left right exterior]
  exact second_grouped_pullback rows repeats path
    (CutSlotAssembly.fill path outside left) (CutSlotAssembly.fill path outside right)
    (CutProjectionAssembly.fillProjection path outside left right p)
    (CutSlotAssembly.fill_outside_eq path outside left right)
    (CutProjectionGeometry.fillProjection_outside path outside left right p)
    (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder right exterior)
    direction _

end Filled
end
end PerfectCompleteness.SourceQuestionPairPullback

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_SourceQuestionProjectionWitness
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionProjectionWitness

noncomputable section

open scoped Classical
open RecursiveSpaces

variable {branch : Nat → Nat} {n t v m : Nat}

private theorem projectionCast_apply_heq
    {left native right : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (h : left = native)
    (p : ∀ leaf k, MixedSupport.Projection (left leaf k) (right leaf k))
    (leaf : Slots branch (n + 1)) (k : Fin t) :
    HEq (CutNativeForms.projectionCast h rfl p leaf k) (p leaf k) := by
  cases h
  rfl

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
  (raw : (i : Fin (branch n)) → SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)

theorem projection_observe :
    SourceProjectedTag.projection clauses designated q choices
        (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)) =
      SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw := by
  funext leaf k
  have htag : HEq
      (SourceProjectedTag.projection clauses designated q choices
        (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)) leaf k)
      (SourceChildKernel.parentProjection rows clauses designated
        (SourceQuestionKernelJoint.sources designated q choices) raw leaf k) := by
    unfold SourceProjectedTag.projection
    dsimp only [id]
    exact mpr_heq _ _
  have hnative := projectionCast_apply_heq
    (SourceQuestionUnmarkedRange.leftSlots_eq clauses designated q choices)
    (SourceChildKernel.parentProjection rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw) leaf k
  exact eq_of_heq (htag.trans hnative.symm)

end
end PerfectCompleteness.SourceQuestionProjectionWitness

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_SourceQuestionTaggedProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionTaggedProjection

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t v m : Nat} {C : Type*} [Fintype C]

omit [Fintype C] in
private theorem castRaw_apply (rows : Nat → Nat)
    {left native : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (h : left = native) (block : CutChildGrouping.Raw (C := C) left rows)
    (i : Fin (branch n)) :
    (cast (congrArg (fun slots => CutChildGrouping.Raw (C := C) slots rows) h) block) i =
      cast (congrArg (fun slots => ChildCallNumbering.Raw (C := C) rows (childSlots slots i)) h)
        (block i) := by
  cases h
  rfl

omit [Fintype C] in
private theorem castRaw_pullback (rows : Nat → Nat)
    {left native right : Slots branch (n + 1) → Fin t → MixedSupport.Slot}
    (h : left = native)
    (p : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (block : CutChildGrouping.Raw (C := C) right rows) :
    cast (congrArg (fun slots => CutChildGrouping.Raw (C := C) slots rows) h)
        (ChildAssemblyProjection.rawPullback rows p block) =
      ChildAssemblyProjection.rawPullback rows (CutNativeForms.projectionCast h rfl p) block := by
  cases h
  rfl

variable (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := n) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := n) (t := t))
  (raw : (i : Fin (branch n)) → SourceChildKernel.Raw (C := C) (t := t) rows clauses designated i)

theorem projection_observe :
    SourceProjectedTag.projection clauses designated q choices
        (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)) =
      SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw :=
  SourceQuestionProjectionWitness.projection_observe rows clauses designated q choices raw

theorem markedBlocks_snd_cast :
    (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2 =
      cast (congrArg (fun slots => CutChildGrouping.Raw (C := C) slots rows)
        (SourceQuestionUnmarkedRange.leftSlots_eq clauses designated q choices))
        (SourceChildKernel.leftChildren rows clauses designated
          (SourceQuestionKernelJoint.sources designated q choices) raw) := by
  funext i
  rw [castRaw_apply rows
    (SourceQuestionUnmarkedRange.leftSlots_eq clauses designated q choices)]
  rfl

theorem markedBlocks_snd :
    (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2 =
      ChildAssemblyProjection.rawPullback rows
        (SourceProjectedTag.projection clauses designated q choices
          (fun i => SourceChildKernel.rawProjected rows clauses designated i (raw i)))
        (SourcePhysicalTaggedChildren.observe rows clauses designated
          (SourceQuestionKernelJoint.sources designated q choices) raw).2 := by
  rw [projection_observe]
  rw [markedBlocks_snd_cast]
  exact castRaw_pullback rows
    (SourceQuestionUnmarkedRange.leftSlots_eq clauses designated q choices)
    (SourceChildKernel.parentProjection rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)
    (SourceChildKernel.rightChildren rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw)

end
end PerfectCompleteness.SourceQuestionTaggedProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_SourceQuestionPhysicalCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPhysicalCollision

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch rows repeats : Nat → Nat} {n height t v m : Nat}
  (path : Path branch n (height + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)
  (placeholder : Slots branch (height + 1) → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch height) → Slots branch height)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hbranch : ∀ k < n, 0 < branch k)
  {adviceRows : Nat} (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
  (exterior : CleanPhysicalReplay.Exterior rows repeats path outside placeholder)
  (q : SourceQuestionLowerForms.Questions
    (branch := branch) (height := height) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple
    (branch := branch) (n := height) (t := t))
  (direction : BucketSampler.Direction (rows (height + 1)))
  (cutoff : Nat)
  (table : SourceQuestionLowerForms.UpperTable (rows := rows)
    path outside clauses upper level (adviceRows := adviceRows) q)

variable
  (tables : (q : SourceQuestionLowerForms.Questions
      (branch := branch) (height := height) (t := t) (m := m)) →
    SourceQuestionLowerForms.UpperTable (rows := rows)
      path outside clauses upper level (adviceRows := adviceRows) q)

theorem rawEvent_observe_oai
    (raw : SourceChildKernelJoint.RawTuple
      (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
      (t := t) rows clauses designated) :
    let observed := SourcePhysicalTaggedChildren.observe rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw
    rawEvent path outside placeholder clauses designated upper level d hbranch A exterior
        q choices direction cutoff (tables q) observed.1 observed.2 =
      SourceQuestionCollisionTransport.globalRestricted path outside placeholder clauses
        upper level d hbranch A exterior tables cutoff designated q choices raw direction := by
  let observed :
      Σ flags : SourceProjectedTag.Flags (branch := branch) (n := height),
        CutChildGrouping.Raw
          (C := SourceQuestionLowerForms.Calls (rows := rows) (repeats := repeats) path)
          (SourceProjectedTag.mixedInside clauses designated q choices flags) rows :=
    SourcePhysicalTaggedChildren.observe rows clauses designated
      (SourceQuestionKernelJoint.sources designated q choices) raw
  let first : SourceQuestionLowerForms.Raw (rows := rows) (repeats := repeats) path clauses q →
      Arrays (SourceQuestionLowerForms.slots path outside clauses q) rows := fun record =>
    LowerCutPair.first rows repeats path (SourceQuestionLowerForms.slots path outside clauses q)
      (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
        (SourceChildMarkedLaw.questionSlots clauses q) exterior)
      (SourceQuestionLowerForms.rawAtCut path outside clauses q record)
  let second : SourceQuestionLowerForms.Raw (rows := rows) (repeats := repeats) path clauses q →
      Arrays (SourceQuestionLowerForms.slots path outside clauses q) rows := fun record =>
    LowerCutPair.second rows repeats path (SourceQuestionLowerForms.slots path outside clauses q)
      (CleanPhysicalReplay.exteriorAt rows repeats path outside placeholder
        (SourceChildMarkedLaw.questionSlots clauses q) exterior) direction
      (SourceQuestionLowerForms.rawAtCut path outside clauses q record)
  let read : Arrays (SourceQuestionLowerForms.slots path outside clauses q) rows →
      Option (BilinearCollisionTransfer.Form (𝕜 := F2)
        (H := HierarchicalDecoderTables.LowerH
          (SourceQuestionLowerForms.slots path outside clauses q) upper level d)) := fun arrays =>
    (LowerCutDecoderForm.answer (SourceQuestionLowerForms.slots path outside clauses q)
      upper level d hbranch A (tables q) cutoff arrays).map
        (OddListExtraction.multiplicationForm (HierarchicalDecoderTables.LowerH
          (SourceQuestionLowerForms.slots path outside clauses q) upper level d))
  have hfirst := SourceQuestionPairPullback.first_pullback rows repeats path outside placeholder
    (SourceChildMarkedLaw.questionSlots clauses q)
    (SourceProjectedTag.mixedInside clauses designated q choices observed.1)
    (SourceProjectedTag.projection clauses designated q choices observed.1)
    exterior observed.2
  have hsecond := SourceQuestionPairPullback.second_pullback rows repeats path outside placeholder
    (SourceChildMarkedLaw.questionSlots clauses q)
    (SourceProjectedTag.mixedInside clauses designated q choices observed.1)
    (SourceProjectedTag.projection clauses designated q choices observed.1)
    exterior direction observed.2
  have hrecord : (SourceChildMarkedLaw.markedBlocks rows clauses designated q choices raw).2 =
      ChildAssemblyProjection.rawPullback rows
        (SourceProjectedTag.projection clauses designated q choices observed.1) observed.2 :=
    SourceQuestionTaggedProjection.markedBlocks_snd rows clauses designated q choices raw
  have hfirstForm := congrArg read (hfirst.trans (congrArg first hrecord.symm))
  have hsecondForm := congrArg read (hsecond.trans (congrArg second hrecord.symm))
  have hinside : SourceProjectedTag.projection clauses designated q choices observed.1 =
      SourceQuestionUnmarkedRange.projection rows clauses designated q choices raw :=
    SourceQuestionTaggedProjection.projection_observe rows clauses designated q choices raw
  have hprojection :
      SourceQuestionPhysicalHigh.projection path outside clauses designated q choices observed.1 =
        SourceQuestionCollisionTransport.projection path outside clauses designated q choices raw :=
    congrArg (CutProjectionAssembly.fillProjection path outside
      (SourceChildMarkedLaw.questionSlots clauses q)
      (SourceProjectedTag.mixedInside clauses designated q choices observed.1)) hinside
  have hspace := congrArg (fun projection : ∀ leaf j, MixedSupport.Projection
      (SourceQuestionLowerForms.slots path outside clauses q leaf j)
      (SourceQuestionPhysicalHigh.projectedSlots path outside clauses designated
        q choices observed.1 leaf j) =>
    LinearMap.range (HPullback (ChildBlockProjection.nodeProjection projection
      (HierarchicalLeftDecoder.LowerNode upper level d)))) hprojection
  exact congrArg₂ (fun (pair : _ × _) space =>
    BilinearCollisionTransfer.restrictedCollision pair.1 pair.2 space)
    (congrArg₂ Prod.mk hfirstForm hsecondForm) hspace

end
end PerfectCompleteness.SourceQuestionPhysicalCollision

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.SourceQuestionPhysicalCollision.rawEvent_observe_oai := @OAI.PerfectCompleteness.SourceQuestionPhysicalCollision.rawEvent_observe_oai
