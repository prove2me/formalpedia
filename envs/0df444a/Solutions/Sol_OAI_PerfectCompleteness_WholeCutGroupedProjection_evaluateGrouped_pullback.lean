-- Prove2me | solution 1 for OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:10.045723+00:00
-- url     : https://prove2.me/submissions/5da55b5f-6283-434d-981d-49611ff58769

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
import Definitions.Def_OAIQ252P012
import Definitions.Def_OAIQ252P015

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

theorem evaluateGrouped_pullback_oai (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
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

end
end PerfectCompleteness.WholeCutGroupedProjection

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback_oai := @OAI.PerfectCompleteness.WholeCutGroupedProjection.evaluateGrouped_pullback_oai
