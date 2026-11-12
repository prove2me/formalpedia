-- Prove2me | solution 1 for OAI.PerfectCompleteness.CleanNativeReplay.rightReplay_heq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:17.224423+00:00
-- url     : https://prove2.me/submissions/283e0ea2-d7a7-4691-aec0-2f02408ce3cf

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

end
end PerfectCompleteness.CutTerminalZero

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerKeyLocalityLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.CutSamplerReplayGrouping

open RecursiveSpaces DescendantSpaces RecursiveSampler TerminalCalls PointwiseSpaces

noncomputable section

universe u w

variable {branch : Nat → Nat} {n m : Nat}

theorem subExterior_splitTape (𝕜 : Type w) [Field 𝕜] (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n (m + 1))
    (A : Slots branch (n + 1) → Type u)
    (tape : CutSamplerRefinement.Tape 𝕜 repeats (.step i p) A)
    (h : Fin (repeats (n + 1))) (b : Bool) :
    subExterior 𝕜 repeats i p A (h, b)
        (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).2 =
      (CutTerminalSplit.splitTape 𝕜 repeats p (childFamily A i)
        (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)).2 := by
  funext j
  rfl

theorem assemble_splitTape (𝕜 : Type w) [Field 𝕜]
    (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (A : Slots branch n → Type u) (clean : Fin (branch m) → Prop)
      (tape : CutSamplerRefinement.Tape 𝕜 repeats p A),
      assemble 𝕜 repeats p A clean (CutTerminalSplit.splitTape 𝕜 repeats p A tape).2
          (fun terminal child =>
            (CutTerminalSplit.splitTape 𝕜 repeats p A tape).1 terminal child.val) =
        CutSamplerReplay.erase 𝕜 repeats p A clean tape := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro A clean tape
          rfl
      | step i p =>
          intro A clean tape
          apply Prod.ext
          · funext j
            rfl
          · funext call
            rcases call with ⟨h, b⟩
            change assemble 𝕜 repeats p (childFamily A i) clean
                (subExterior 𝕜 repeats i p A (h, b)
                  (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).2)
                (fun terminal child =>
                  (CutTerminalSplit.splitTape 𝕜 repeats (.step i p) A tape).1
                    ((h, b), terminal) child.val) =
              CutSamplerReplay.erase 𝕜 repeats p (childFamily A i) clean
                (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)
            rw [subExterior_splitTape]
            simp_rw [CutTerminalZero.splitTape_terminal_step]
            exact ih p (childFamily A i) clean
              (CutSamplerLocality.subTape 𝕜 repeats i p A tape h b)

end
end PerfectCompleteness.CutSamplerReplayGrouping

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplayGrouping

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

theorem assemble_splitTape (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop) (tape : WholeCutSampler.Tape rows repeats p slots),
      assemble rows repeats p slots clean
          (WholeCutGrouping.splitTape rows repeats p slots tape).1
          (fun child => (WholeCutGrouping.splitTape rows repeats p slots tape).2 child.val) =
        WholeCutReplay.erase rows repeats p slots clean tape := by
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
          apply Prod.ext
          · funext bucket
            exact CutSamplerReplayGrouping.assemble_splitTape F2 repeats (.step i p)
              (LeafDomain slots) clean (tape.1 bucket)
          · apply Prod.ext
            · exact ih p (childSlots slots i) clean tape.2.1
            · rfl

end
end PerfectCompleteness.WholeCutReplayGrouping

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CutSamplerReplayGroupingTransport
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
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

variable {branch : Nat → Nat} {n m t : Nat}

theorem squareEquiv_eq_cast
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (f : squareSpace (H slots)) :
    (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
        (fun s => Equiv.cast (congrArg MixedSupport.Assignment (congrFun hs s)))).symm f =
      cast (congrArg
        (fun ss : Slots branch n → Fin t → MixedSupport.Slot => (squareSpace (H ss) : Type))
        hs) f := by
  cases hs
  apply Subtype.ext
  funext x
  rfl

theorem subExterior_cast (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots target : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf (.step i p) clean s → slots s = target s)
    (call : Fin (repeats (n + 1)) × Bool)
    (exterior : CutTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain slots)) :
    CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain target) call
        (cast (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
          (outside_eq (.step i p) slots target clean hs)) exterior) =
      cast (WholeCutExteriorTransport.scalarExterior_eq repeats p
        (childSlots slots i) (childSlots target i)
        (outside_eq p (childSlots slots i) (childSlots target i) clean
          (fun s h => hs (i, s) (Or.inr h))))
        (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain slots) call exterior) := by
  funext j
  let hext := WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
    (outside_eq (.step i p) slots target clean hs)
  let hsub := WholeCutExteriorTransport.scalarExterior_eq repeats p
    (childSlots slots i) (childSlots target i)
    (outside_eq p (childSlots slots i) (childSlots target i) clean
      (fun s h => hs (i, s) (Or.inr h)))
  change (cast hext exterior) (CutSamplerReplayGrouping.exteriorStepIndex repeats i p call j) =
    (cast hsub
      (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain slots) call exterior)) j
  rw [cast_pi_apply hext
    (fun j => WholeCutExteriorTransport.factor_eq repeats (.step i p) slots target
      (outside_eq (.step i p) slots target clean hs) j.val j.property)]
  rw [cast_pi_apply hsub
    (fun j => WholeCutExteriorTransport.factor_eq repeats p (childSlots slots i)
      (childSlots target i)
      (outside_eq p (childSlots slots i) (childSlots target i) clean
        (fun s h => hs (i, s) (Or.inr h))) j.val j.property)]
  rfl

theorem transport_assemble (repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (hs : ∀ s, keptLeaf p clean s → slots s = target s)
      (exterior : CutTerminalSplit.ExteriorTape F2 repeats p (LeafDomain slots))
      (terminal : CutSamplerReplayGrouping.RetainedTerminal F2 repeats p (LeafDomain slots) clean),
      CutSamplerReplayTransport.transport F2 repeats p (LeafDomain slots) (LeafDomain target)
          clean (WholeCutReplayKeys.leafEquiv p slots target clean hs)
          (CutSamplerReplayGrouping.assemble F2 repeats p (LeafDomain slots) clean exterior terminal) =
        CutSamplerReplayGrouping.assemble F2 repeats p (LeafDomain target) clean
          (cast (WholeCutExteriorTransport.scalarExterior_eq repeats p slots target
            (outside_eq p slots target clean hs)) exterior)
          (castTerminal repeats p slots target clean hs terminal) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots target clean hs exterior terminal
          funext child
          exact squareEquiv_eq_cast (childSlots slots child.val) (childSlots target child.val)
            (retainedChildSlots_eq (.refl (n + 1)) slots target clean hs child) (terminal () child)
      | step i p =>
          intro slots target clean hs exterior terminal
          apply Prod.ext
          · funext j
            let hext := WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p)
              slots target (outside_eq (.step i p) slots target clean hs)
            let hslots := WholeCutExteriorTransport.ordinarySlots_eq i p slots target
              (outside_eq (.step i p) slots target clean hs) j
            change (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
                (fun s => WholeCutReplayKeys.leafEquiv (.step i p) slots target clean hs
                  (j.val, s) (Or.inl j.property))).symm
                (exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩) =
              (cast hext exterior) ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩
            rw [cast_pi_apply hext
              (fun j => WholeCutExteriorTransport.factor_eq repeats (.step i p) slots target
                (outside_eq (.step i p) slots target clean hs) j.val j.property)]
            exact squareEquiv_eq_cast (childSlots slots j.val) (childSlots target j.val) hslots
              (exterior ⟨.inl j, not_isTerminal_ordinary repeats i p j⟩)
          · funext call
            change CutSamplerReplayTransport.transport F2 repeats p
                (LeafDomain (childSlots slots i)) (LeafDomain (childSlots target i)) clean
                (WholeCutReplayKeys.leafEquiv p (childSlots slots i) (childSlots target i) clean
                  (fun s h => hs (i, s) (Or.inr h)))
                (CutSamplerReplayGrouping.assemble F2 repeats p (LeafDomain (childSlots slots i))
                  clean (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain slots)
                    call exterior) (fun location child => terminal (call, location) child)) =
              CutSamplerReplayGrouping.assemble F2 repeats p (LeafDomain (childSlots target i))
                clean (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain target) call
                  (cast (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
                    (outside_eq (.step i p) slots target clean hs)) exterior))
                (fun location child => castTerminal repeats (.step i p) slots target clean hs
                  terminal (call, location) child)
            rw [subExterior_cast repeats i p slots target clean hs call exterior]
            exact ih p (childSlots slots i) (childSlots target i) clean
              (fun s h => hs (i, s) (Or.inr h))
              (CutSamplerReplayGrouping.subExterior F2 repeats i p (LeafDomain slots) call exterior)
              (fun location child => terminal (call, location) child)

end
end PerfectCompleteness.CutSamplerReplayGroupingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeCutReplayGroupingTransport
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.WholeCutReplayGroupingTransport

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open CutSamplerKeyLocality
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {n m t : Nat}

export CutSamplerReplayGroupingTransport (outside_kept outside_eq retainedChildSlots_eq)

theorem castChildren_apply_heq (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean)
    (child : {i : Fin (branch m) // ¬ clean i}) :
    HEq (castChildren rows repeats p slots target clean hs children child) (children child) :=
  cast_heq _ _

private theorem blockCast_calls {C : Type} (rows : Nat → Nat)
    {slots target : Slots branch m → Fin t → MixedSupport.Slot} (hs : slots = target)
    (x : ChildBlock C rows slots) (c : C) :
    (cast (congrArg (ChildBlock C rows) hs) x).1 c =
      cast (congrArg (fun ss => (PointwiseSpaces.squareSpace (H ss) : Type)) hs) (x.1 c) := by
  cases hs
  rfl

theorem castChildren_calls (rows repeats : Nat → Nat) (p : Path branch n (m + 1))
    (slots target : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf p clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean)
    (child : {i : Fin (branch m) // ¬ clean i}) (c : WholeCutCalls.Index rows repeats p) :
    (castChildren rows repeats p slots target clean hs children child).1 c =
      cast (congrArg (fun ss => (PointwiseSpaces.squareSpace (H ss) : Type))
        (retainedChildSlots_eq p slots target clean hs child)) ((children child).1 c) :=
  blockCast_calls rows (retainedChildSlots_eq p slots target clean hs child) (children child) c

private theorem blockCast_reindex {C D : Type} (rows : Nat → Nat) (f : D → C)
    {slots target : Slots branch m → Fin t → MixedSupport.Slot} (hs : slots = target)
    (x : ChildBlock C rows slots) :
    ((fun d => (cast (congrArg (ChildBlock C rows) hs) x).1 (f d)),
        (cast (congrArg (ChildBlock C rows) hs) x).2) =
      cast (congrArg (ChildBlock D rows) hs) (fun d => x.1 (f d), x.2) := by
  cases hs
  rfl

private theorem blockTransport_eq_cast {C : Type} (rows : Nat → Nat)
    (slots target : Slots branch m → Fin t → MixedSupport.Slot) (hs : slots = target)
    (x : ChildBlock C rows slots) :
    ((fun c => (RecursiveSpaceEquiv.squareEquiv (𝕜 := F2)
        (fun s => Equiv.cast (congrArg MixedSupport.Assignment (congrFun hs s)))).symm (x.1 c)),
      WholeCutReplayTransport.arraysTransport rows slots target
        (fun s => Equiv.cast (congrArg MixedSupport.Assignment (congrFun hs s))) x.2) =
      cast (congrArg (ChildBlock C rows) hs) x := by
  cases hs
  apply Prod.ext
  · funext c
    apply Subtype.ext
    funext y
    rfl
  · funext node row
    apply Subtype.ext
    funext y
    rfl

private theorem arraysTransport_eq_cast (rows : Nat → Nat)
    (slots target : Slots branch n → Fin t → MixedSupport.Slot) (hs : slots = target)
    (arrays : Arrays slots rows) :
    WholeCutReplayTransport.arraysTransport rows slots target
        (fun s => Equiv.cast (congrArg MixedSupport.Assignment (congrFun hs s))) arrays =
      cast (congrArg (fun ss => Arrays ss rows) hs) arrays := by
  cases hs
  funext node row
  apply Subtype.ext
  funext y
  rfl

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
    (slots target : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf (.step i p) clean s → slots s = target s)
    (ext : WholeCutGrouping.Exterior rows repeats (.step i p) slots) :
    WholeCutExteriorTransport.equiv rows repeats (.step i p) slots target
        (outside_eq (.step i p) slots target clean hs) ext =
      (fun bucket => cast
        (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
          (outside_eq (.step i p) slots target clean hs)) (ext.1 bucket),
        (WholeCutExteriorTransport.equiv rows repeats p (childSlots slots i) (childSlots target i)
          (outside_eq p (childSlots slots i) (childSlots target i) clean
            (fun s h => hs (i, s) (Or.inr h))) ext.2.1,
          fun j => cast (congrArg (fun ss => Arrays ss rows)
            (WholeCutExteriorTransport.ordinarySlots_eq i p slots target
              (outside_eq (.step i p) slots target clean hs) j)) (ext.2.2 j))) :=
  cast_exterior_parts _ _ _ _ ext

private theorem castChildren_tail (rows repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n (m + 1))
    (slots target : Slots branch (n + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch m) → Prop)
    (hs : ∀ s, keptLeaf (.step i p) clean s → slots s = target s)
    (children : WholeCutReplayGrouping.RetainedChildren rows repeats (.step i p) slots clean) :
    (fun child =>
      (fun q => (castChildren rows repeats (.step i p) slots target clean hs children child).1 (.inr q),
        (castChildren rows repeats (.step i p) slots target clean hs children child).2)) =
      castChildren rows repeats p (childSlots slots i) (childSlots target i) clean
        (fun s h => hs (i, s) (Or.inr h))
        (fun child => (fun q => (children child).1 (.inr q), (children child).2)) := by
  funext child
  exact blockCast_reindex rows Sum.inr
    (retainedChildSlots_eq (.step i p) slots target clean hs child) (children child)

theorem transport_assemble (rows repeats : Nat → Nat) (p : Path branch n (m + 1)) :
    ∀ (slots target : Slots branch n → Fin t → MixedSupport.Slot)
      (clean : Fin (branch m) → Prop)
      (hs : ∀ s, keptLeaf p clean s → slots s = target s)
      (ext : WholeCutGrouping.Exterior rows repeats p slots)
      (children : WholeCutReplayGrouping.RetainedChildren rows repeats p slots clean),
    WholeCutReplayKeys.transportTape rows repeats p slots target clean hs
        (WholeCutReplayGrouping.assemble rows repeats p slots clean ext children) =
      WholeCutReplayGrouping.assemble rows repeats p target clean
        (WholeCutExteriorTransport.equiv rows repeats p slots target
          (outside_eq p slots target clean hs) ext)
        (castChildren rows repeats p slots target clean hs children) := by
  induction n generalizing m with
  | zero =>
      have h := p.height_le
      omega
  | succ n ih =>
      cases p with
      | refl =>
          intro slots target clean hs ext children
          funext child
          exact blockTransport_eq_cast rows _ _
            (retainedChildSlots_eq (.refl (n + 1)) slots target clean hs child) (children child)
      | step i p =>
          intro slots target clean hs ext children
          rw [exterior_equiv_step rows repeats i p slots target clean hs ext]
          apply Prod.ext
          · funext bucket
            refine (CutSamplerReplayGroupingTransport.transport_assemble repeats (.step i p)
              slots target clean hs (ext.1 bucket)
              (fun terminal child => (children child).1 (.inl (bucket, terminal)))).trans ?_
            let exterior : CutTerminalSplit.ExteriorTape F2 repeats (.step i p) (LeafDomain target) :=
              cast (WholeCutExteriorTransport.scalarExterior_eq repeats (.step i p) slots target
                (outside_eq (.step i p) slots target clean hs)) (ext.1 bucket)
            change CutSamplerReplayGrouping.assemble F2 repeats (.step i p)
                (LeafDomain target) clean exterior
                (CutSamplerReplayGroupingTransport.castTerminal repeats (.step i p)
                  slots target clean hs
                  (fun terminal child => (children child).1 (.inl (bucket, terminal)))) =
              CutSamplerReplayGrouping.assemble F2 repeats (.step i p)
                (LeafDomain target) clean exterior
                (fun terminal child =>
                  (castChildren rows repeats (.step i p) slots target clean hs children child).1
                    (.inl (bucket, terminal)))
            apply congrArg (CutSamplerReplayGrouping.assemble F2 repeats (.step i p)
              (LeafDomain target) clean exterior)
            funext terminal child
            exact (castChildren_calls rows repeats (.step i p) slots target clean hs
              children child (.inl (bucket, terminal))).symm
          · apply Prod.ext
            · refine (ih p (childSlots slots i) (childSlots target i) clean
                (fun s h => hs (i, s) (Or.inr h)) ext.2.1
                (fun child => (fun q => (children child).1 (.inr q), (children child).2))).trans ?_
              let exterior : WholeCutGrouping.Exterior rows repeats p (childSlots target i) :=
                WholeCutExteriorTransport.equiv rows repeats p (childSlots slots i) (childSlots target i)
                  (outside_eq p (childSlots slots i) (childSlots target i) clean
                    (fun s h => hs (i, s) (Or.inr h))) ext.2.1
              change WholeCutReplayGrouping.assemble rows repeats p (childSlots target i) clean exterior
                  (castChildren rows repeats p (childSlots slots i) (childSlots target i) clean
                    (fun s h => hs (i, s) (Or.inr h))
                    (fun child => (fun q => (children child).1 (.inr q), (children child).2))) =
                WholeCutReplayGrouping.assemble rows repeats p (childSlots target i) clean exterior
                  (fun child =>
                    (fun q => (castChildren rows repeats (.step i p) slots target clean hs
                      children child).1 (.inr q),
                      (castChildren rows repeats (.step i p) slots target clean hs children child).2))
              apply congrArg (WholeCutReplayGrouping.assemble rows repeats p
                (childSlots target i) clean exterior)
              exact (castChildren_tail rows repeats i p slots target clean hs children).symm
            · funext j
              exact arraysTransport_eq_cast rows _ _
                (WholeCutExteriorTransport.ordinarySlots_eq i p slots target
                  (outside_eq (.step i p) slots target clean hs) j) (ext.2.2 j)

end
end PerfectCompleteness.WholeCutReplayGroupingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanEndpointSlots
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CleanEndpointSlots

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces
open SourceQuestionReconstruction

variable {branch : Nat → Nat} {n h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  (clean : Fin (branch h) → Prop)
  (visible : Visible (E := SourceTuple m t) designated clean)

variable (rows repeats : Nat → Nat) (p : Path branch n (h + 1))
  (outside : Slots branch n → Fin t → MixedSupport.Slot)

omit [NeZero m] in
theorem rightSlots_kept_eq (projected : Fin (branch h) → Bool)
    (own other : {i : Fin (branch h) // clean i} → Fin t → Fin v)
    (s : Slots branch n) (hs : CutSamplerKeyLocality.keptLeaf p clean s) :
    rightSlots clauses designated clean visible p outside projected own s =
      rightSlots clauses designated clean visible p outside projected other s :=
  CutSlotAssembly.fill_kept_eq p outside _ _ clean
    (rightInside_nonclean clauses designated clean visible projected own other) s hs

end
end PerfectCompleteness.CleanEndpointSlots

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanRecordChildBlocks
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
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

theorem rightChild_heq (record : Record (C := C) (t := t) rows clauses designated)
    (i : Nonclean rows clauses designated record) :
    HEq (rightChild rows clauses designated record i)
      (physicalRight rows clauses designated i.val (extract rows clauses designated record i)) :=
  cast_heq _ _

private theorem dependent_congr {A : Sort*} {B : A → Sort*} (f : (a : A) → B a)
    {a b : A} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

theorem rightChild_event_heq (record : Record (C := C) (t := t) rows clauses designated)
    (x : Sample (C := C) (t := t) rows clauses designated)
    (hevent : event rows clauses designated record x = true)
    (i : Nonclean rows clauses designated record) :
    HEq (rightChild rows clauses designated record i)
      (SourceChildKernel.rightChildren rows clauses designated
        (fun j => ((x j).1, (x j).2.1)) (fun j => (x j).2.2) i.val) :=
  (rightChild_heq rows clauses designated record i).trans
    (dependent_congr (physicalRight rows clauses designated i.val)
      (extract_eq rows clauses designated record x hevent i))

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

theorem fillChild_heq (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (i : Fin (branch h))
    (block : CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i) :
    HEq (fillChild rows repeats p outside inside i block) block :=
  cast_heq _ _

theorem assembleAt_eq_erase (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (external : Exterior rows repeats p outside placeholder)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    assembleAt rows repeats p outside placeholder inside clean external (fun i => children i.val) =
      WholeCutReplay.erase rows repeats p (CutSlotAssembly.fill p outside inside) clean
        (physicalTape rows repeats p outside placeholder inside external children) := by
  have h := WholeCutReplayGrouping.assemble_splitTape rows repeats p
    (CutSlotAssembly.fill p outside inside) clean
    (physicalTape rows repeats p outside placeholder inside external children)
  change WholeCutReplayGrouping.assemble rows repeats p (CutSlotAssembly.fill p outside inside) clean
      (exteriorAt rows repeats p outside placeholder inside external)
      (fun child => fillChild rows repeats p outside inside child.val (children child.val)) =
    WholeCutReplay.erase rows repeats p (CutSlotAssembly.fill p outside inside) clean
      (physicalTape rows repeats p outside placeholder inside external children)
  simpa only [physicalTape, Equiv.apply_symm_apply] using h

private theorem exteriorAt_heq
    (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (external : Exterior rows repeats p outside placeholder) :
    HEq (exteriorAt rows repeats p outside placeholder inside external) external :=
  cast_heq _ _

theorem transport_assembleAt
    (inside target : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop)
    (hs : ∀ i, ¬ clean i → ∀ s, inside (i, s) = target (i, s))
    (external : Exterior rows repeats p outside placeholder)
    (children : (i : {i : Fin (branch h) // ¬ clean i}) →
      CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) inside rows i.val)
    (other : (i : {i : Fin (branch h) // ¬ clean i}) →
      CutChildGrouping.Child (C := WholeCutCalls.Index rows repeats p) target rows i.val)
    (hc : ∀ i, HEq (children i) (other i)) :
    WholeCutReplayKeys.transportTape rows repeats p
        (CutSlotAssembly.fill p outside inside) (CutSlotAssembly.fill p outside target) clean
        (CutSlotAssembly.fill_kept_eq p outside inside target clean hs)
        (assembleAt rows repeats p outside placeholder inside clean external children) =
      assembleAt rows repeats p outside placeholder target clean external other := by
  unfold assembleAt
  rw [WholeCutReplayGroupingTransport.transport_assemble]
  apply congrArg₂ (WholeCutReplayGrouping.assemble rows repeats p
    (CutSlotAssembly.fill p outside target) clean)
  · apply eq_of_heq
    exact (cast_heq _ _).trans
      ((exteriorAt_heq rows repeats p outside placeholder inside external).trans
        (exteriorAt_heq rows repeats p outside placeholder target external).symm)
  · funext i
    apply eq_of_heq
    exact (WholeCutReplayGroupingTransport.castChildren_apply_heq rows repeats p
      (CutSlotAssembly.fill p outside inside) (CutSlotAssembly.fill p outside target) clean
      (CutSlotAssembly.fill_kept_eq p outside inside target clean hs)
      (retainedAt rows repeats p outside inside clean children) i).trans
        ((fillChild_heq rows repeats p outside inside i.val (children i)).trans
          ((hc i).trans (fillChild_heq rows repeats p outside target i.val (other i)).symm))

section Source

variable {v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

theorem rightRecord_eq_erase (record : Record (t := t) rows repeats p clauses designated)
    (x : Sample (t := t) rows repeats p clauses designated)
    (hevent : CleanRecordChildBlocks.event rows clauses designated record x = true)
    (external : Exterior rows repeats p outside placeholder) :
    WholeCutReplayKeys.transportTape rows repeats p
      (CutSlotAssembly.fill p outside (CleanRecordChildBlocks.rightRef rows clauses designated record))
      (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (CutSlotAssembly.fill_kept_eq p outside _ _ _
        (rightInside_nonclean rows repeats p clauses designated record x hevent))
      (rightRecord rows repeats p outside placeholder clauses designated record external) =
    WholeCutReplay.erase rows repeats p
      (CutSlotAssembly.fill p outside (rightInside rows repeats p clauses designated x))
      (CleanRecordChildBlocks.clean rows clauses designated record)
      (rightTape rows repeats p outside placeholder clauses designated x external) := by
  exact (transport_assembleAt rows repeats p outside placeholder _ _ _
    (rightInside_nonclean rows repeats p clauses designated record x hevent) external _ _
    (CleanRecordChildBlocks.rightChild_event_heq rows clauses designated record x hevent)).trans
      (assembleAt_eq_erase rows repeats p outside placeholder _ _ external
        (rightBlocks rows repeats p clauses designated x))

end Source

end
end PerfectCompleteness.CleanPhysicalReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanNativeReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

private theorem transport_target_heq (rows repeats : Nat → Nat)
    (p : Path branch n (h + 1))
    (reference target other : Slots branch n → Fin t → MixedSupport.Slot)
    (clean : Fin (branch h) → Prop) (heq : target = other)
    (hs : ∀ s, CutSamplerKeyLocality.keptLeaf p clean s → reference s = target s)
    (hs' : ∀ s, CutSamplerKeyLocality.keptLeaf p clean s → reference s = other s)
    (tape : WholeCutReplay.Tape rows repeats p reference clean) :
    HEq (WholeCutReplayKeys.transportTape rows repeats p reference target clean hs tape)
      (WholeCutReplayKeys.transportTape rows repeats p reference other clean hs' tape) := by
  cases heq
  rfl

end Transport

variable {branch rows repeats : Nat → Nat} {n h t v m : Nat} [NeZero m]
  {upper : Nodes branch n} {d : HierarchicalFrozenTables.LowerNodes upper (h + 1)}
  (S : CleanDecoderRate.Setup branch rows repeats n h t v m upper d)

theorem rightReplay_heq_oai (x : CleanDecoderRate.Sample S) :
    HEq (CleanRightDecoder.replay (context S x).clauses (context S x).designated
      (context S x).clean (context S x).visible (context S x).projected upper
      (CleanDecoderContext.lower (context S x)) (context S x).cut
      (CleanDecoderContext.lowerHeight upper d) (context S x).outside rows repeats
      (context S x).rightTape (rightOwn S x))
      (WholeCutReplay.erase rows repeats (CleanDecoderRate.path S) (rightSlots S x)
        (context S x).clean (rightTape S x)) := by
  let record := CleanDecoderRate.observations S x
  have hevent := CleanRecordDecoderInput.event_observe
    rows repeats upper d S.cut S.clauses S.designated x
  have hrecord := CleanPhysicalReplay.rightRecord_eq_erase
    rows repeats (CleanDecoderRate.path S) S.outside S.placeholder S.clauses S.designated
    record x hevent S.exterior
  have htransport := transport_target_heq rows repeats (CleanDecoderRate.path S)
    (CutSlotAssembly.fill (CleanDecoderRate.path S) S.outside
      (CleanRecordChildBlocks.rightRef rows S.clauses S.designated record))
    (CleanDecoderContext.rightSlots (context S x) (rightOwn S x)) (rightSlots S x)
    (context S x).clean (rightSlots_eq S x)
    (CleanEndpointSlots.rightSlots_kept_eq S.clauses S.designated (context S x).clean
      (context S x).visible (CleanDecoderRate.path S) S.outside (context S x).projected
      (fun _ _ => (S.clauses 0).variable 0) (rightOwn S x))
    (CutSlotAssembly.fill_kept_eq (CleanDecoderRate.path S) S.outside _ _ _
      (CleanPhysicalReplay.rightInside_nonclean rows repeats (CleanDecoderRate.path S)
        S.clauses S.designated record x hevent))
    (CleanPhysicalReplay.rightRecord rows repeats (CleanDecoderRate.path S)
      S.outside S.placeholder S.clauses S.designated record S.exterior)
  exact htransport.trans (heq_of_eq hrecord)

end
end PerfectCompleteness.CleanNativeReplay

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.CleanNativeReplay.rightReplay_heq_oai := @OAI.PerfectCompleteness.CleanNativeReplay.rightReplay_heq_oai
