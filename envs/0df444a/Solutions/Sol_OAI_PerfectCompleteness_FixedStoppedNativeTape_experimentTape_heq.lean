-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedNativeTape.experimentTape_heq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:26.140099+00:00
-- url     : https://prove2.me/submissions/5ee506ab-c3c3-43fe-8ad1-c17372a7fe2d

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
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedNativeProjection_rightSlots_eq

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionRawSwap
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionRawSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h n t v m : Nat}

variable {C : Type*} [Fintype C]
  (rows : Nat → Nat) (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch n) → Slots branch n)

theorem sources_insideQuestions_positions
    (sample : SourceChildKernel.Sample (C := C) (t := t) rows clauses designated) :
    SourceQuestionKernelJoint.sources designated
        (insideQuestions rows clauses designated sample)
        (positions rows clauses designated sample) =
      fun child => ((sample child).1, (sample child).2.1) := by
  change (SourceQuestionKernelJoint.sourceEquiv designated).symm
      ((SourceQuestionKernelJoint.sourceEquiv designated)
        (fun child => ((sample child).1, (sample child).2.1))) = _
  exact (SourceQuestionKernelJoint.sourceEquiv designated).symm_apply_apply _

end
end PerfectCompleteness.SourceQuestionRawSwap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_CleanPhysicalReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
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

end
end PerfectCompleteness.CleanPhysicalReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourcePhysicalExteriorSwap
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalExteriorSwap

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))

theorem toCanonical_heq (questions : PreliminarySampler.Questions branch root t m)
    (external : ActualExterior clauses rows repeats p questions) :
    HEq (toCanonical clauses rows repeats p questions external) external :=
  cast_heq _ _

theorem fromCanonical_heq (questions : PreliminarySampler.Questions branch root t m)
    (external : CanonicalExterior clauses rows repeats p
      (SourceQuestionCutSplit.outside p questions)) :
    HEq (fromCanonical clauses rows repeats p questions external) external := by
  exact (toCanonical_heq clauses rows repeats p questions
    (fromCanonical clauses rows repeats p questions external)).symm.trans
      (heq_of_eq ((toCanonical clauses rows repeats p questions).apply_symm_apply external))

end
end PerfectCompleteness.SourcePhysicalExteriorSwap

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedStoppedNativeProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedNativeProjection

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open FixedStoppedPhysicalLaw (clauses designated)

private theorem projectedSlots_physicalRead_eq
    {branch : Nat → Nat} {n i j t v m : Nat} [NeZero m]
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
    (designated : Fin (branch i) → Slots branch i)
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (sample : StoppedProjectedExperiment.PhysicalSample
      clauses rows repeats hupper hij designated o) :
    StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated o
        (StoppedProjectedExperiment.physicalRead clauses rows repeats hupper hij designated o sample).1 =
      SourcePhysicalTapeLaw.projectedSlots
        (StoppedProjectedExperiment.stoppedPath rows hupper hij o
          (StoppedProjectedExperiment.baseTag rows sample.1))
        (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
        (StoppedProjectedExperiment.physicalSources rows hupper hij designated o sample.1,
          (StoppedProjectedExperiment.physicalRead
            clauses rows repeats hupper hij designated o sample).1.2.1.2) := rfl

private theorem projectedSlots_tag_eq_rightSlots
    {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
    (rows repeats : Nat → Nat) (p : Path branch root (h + 1))
    (outside : Slots branch root → Fin t → MixedSupport.Slot)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch h) → Slots branch h)
    (sample : SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated) :
    SourcePhysicalTapeLaw.projectedSlots p outside clauses designated
        (SourcePhysicalTapeLaw.tag rows repeats p clauses designated sample) =
      CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated sample := rfl

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

theorem physicalSources_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    StoppedProjectedExperiment.physicalSources (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
      (physicalSample parameters i j hij input sample).1
      (physicalSample parameters i j hij input sample).2.1.1 =
      sources parameters i j hij input sample := by
  change SourceQuestionKernelJoint.sources (designated parameters i)
      (SourceQuestionCutSplit.restrict (path parameters i j hij input sample)
        (SourceQuestionCutSplit.join (path parameters i j hij input sample)
          (SourceQuestionRawSwap.insideQuestions (FixedRows.rows parameters.plan)
            (clauses input) (designated parameters i) (childSample parameters i j hij input sample))
          sample.1.2.1))
      (SourceQuestionRawSwap.positions (FixedRows.rows parameters.plan)
        (clauses input) (designated parameters i) (childSample parameters i j hij input sample)) = _
  have hrestrict := SourceQuestionRawSwap.restrict_join (path parameters i j hij input sample)
    (SourceQuestionRawSwap.insideQuestions (FixedRows.rows parameters.plan)
      (clauses input) (designated parameters i) (childSample parameters i j hij input sample))
    sample.1.2.1
  have hsources := congrArg (fun questions => SourceQuestionKernelJoint.sources
    (designated parameters i) questions
    (SourceQuestionRawSwap.positions (FixedRows.rows parameters.plan)
      (clauses input) (designated parameters i) (childSample parameters i j hij input sample))) hrestrict
  exact hsources.trans
    (SourceQuestionRawSwap.sources_insideQuestions_positions (FixedRows.rows parameters.plan)
      (clauses input) (designated parameters i) (childSample parameters i j hij input sample))

theorem physicalRightSlots_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (innerTag parameters i j hij input sample) =
      CleanPhysicalCanonicalQuery.rightSlots (FixedRows.rows parameters.plan)
        (FixedRows.repeats parameters.plan) (path parameters i j hij input sample)
        (StoppedProjectedExperiment.nativeSlots (clauses input)
          (physicalSample parameters i j hij input sample).1)
        (clauses input) (designated parameters i) (childSample parameters i j hij input sample) := by
  have hread := projectedSlots_physicalRead_eq (clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (physicalSample parameters i j hij input sample).1
    (physicalSample parameters i j hij input sample).2.1
  have htags := congrArg₂ Prod.mk (physicalSources_eq parameters i j hij input sample)
    (flags_eq parameters i j hij input sample)
  have hslots := congrArg (SourcePhysicalTapeLaw.projectedSlots
    (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1) (clauses input) (designated parameters i)) htags
  have hright := projectedSlots_tag_eq_rightSlots (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1) (clauses input) (designated parameters i)
    (childSample parameters i j hij input sample)
  exact hread.trans (hslots.trans hright)

end
end PerfectCompleteness.FixedStoppedNativeProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SourcePhysicalExteriorReplay
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourcePhysicalExteriorReplay

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {root h t : Nat}
  (rows repeats : Nat → Nat) (p : Path branch root (h + 1))

private theorem splitTape_symm_heq
    {slots target : Slots branch root → Fin t → MixedSupport.Slot}
    (hslots : slots = target)
    (external : WholeCutGrouping.Exterior rows repeats p slots)
    (other : WholeCutGrouping.Exterior rows repeats p target)
    (hext : HEq external other)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p slots) rows)
    (otherChildren : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p)
      (WholeCutGrouping.cutSlots p target) rows)
    (hchildren : ∀ child, HEq (children child) (otherChildren child)) :
    HEq ((WholeCutGrouping.splitTape rows repeats p slots).symm (external, children))
      ((WholeCutGrouping.splitTape rows repeats p target).symm (other, otherChildren)) := by
  cases hslots
  have he : external = other := eq_of_heq hext
  have hc : children = otherChildren := funext (fun child => eq_of_heq (hchildren child))
  cases he
  cases hc
  rfl

theorem physicalTape_heq
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder otherPlaceholder inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (hfill : CutSlotAssembly.fill p outside inside = CutSlotAssembly.fill p otherOutside inside)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (other : CleanPhysicalReplay.Exterior rows repeats p otherOutside otherPlaceholder)
    (hext : HEq external other)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    HEq (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside external children)
      (CleanPhysicalReplay.physicalTape rows repeats p otherOutside otherPlaceholder inside other children) := by
  apply splitTape_symm_heq rows repeats p hfill
  · exact (cast_heq _ _).trans (hext.trans (cast_heq _ _).symm)
  · intro child
    exact (CleanPhysicalReplay.fillChild_heq rows repeats p outside inside child (children child)).trans
      (CleanPhysicalReplay.fillChild_heq rows repeats p otherOutside inside child (children child)).symm

private theorem collapse_heq
    {slots target : Slots branch root → Fin t → MixedSupport.Slot}
    (hslots : slots = target)
    (tape : WholeCutSampler.Tape rows repeats p slots)
    (other : WholeCutSampler.Tape rows repeats p target) (htape : HEq tape other) :
    HEq (WholeCutSampler.collapse rows repeats p slots tape)
      (WholeCutSampler.collapse rows repeats p target other) := by
  cases hslots
  cases htape
  rfl

theorem collapsedTape_heq
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder otherPlaceholder inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (hfill : CutSlotAssembly.fill p outside inside = CutSlotAssembly.fill p otherOutside inside)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (other : CleanPhysicalReplay.Exterior rows repeats p otherOutside otherPlaceholder)
    (hext : HEq external other)
    (children : CutChildGrouping.Raw (C := WholeCutCalls.Index rows repeats p) inside rows) :
    HEq (WholeCutSampler.collapse rows repeats p (CutSlotAssembly.fill p outside inside)
      (CleanPhysicalReplay.physicalTape rows repeats p outside placeholder inside external children))
      (WholeCutSampler.collapse rows repeats p (CutSlotAssembly.fill p otherOutside inside)
        (CleanPhysicalReplay.physicalTape rows repeats p otherOutside otherPlaceholder inside other children)) :=
  collapse_heq rows repeats p hfill _ _
    (physicalTape_heq rows repeats p outside otherOutside placeholder otherPlaceholder inside
      hfill external other hext children)

end
end PerfectCompleteness.SourcePhysicalExteriorReplay

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_StoppedCleanOwnInputGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedCleanOwnInputGeometry

noncomputable section

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat} (rows repeats : Nat → Nat)

theorem pathTapeEquiv_heq
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    {p q : Σ height, Path branch n height} (hp : p = q)
    (tape : WholeArraySampler.Tape rows repeats p.2 slots) :
    HEq (StoppedOwnInputGeometry.pathTapeEquiv rows repeats slots hp tape) tape :=
  cast_heq _ _

theorem uncastTape_heq
    (slots : Slots branch n → Fin t → MixedSupport.Slot)
    (upper lower : Nodes branch n) (cut : OwnInputReference.Cut upper lower)
    {k : Nat} (hk : Nodes.height lower = k)
    (tape : WholeArraySampler.Tape rows repeats
      ((Nodes.path upper).append (hk ▸ cut.path)) slots) :
    HEq (CleanPhysicalDecoderLaw.uncastTape slots upper lower cut hk tape) tape := by
  cases hk
  rfl

end
end PerfectCompleteness.StoppedCleanOwnInputGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FixedStoppedNativeTape
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedNativeTape

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open FixedStoppedPhysicalLaw (clauses designated)
open FixedStoppedNativeProjection (physicalSample innerTag path childSample)

private theorem cast_trans_toFun_heq {α β γ : Type}
    (h : α = β) (e : β ≃ γ)
    (he : ∀ b : β, HEq (@Equiv.toFun β γ e b) b) (a : α) :
    HEq (@Equiv.toFun α γ ((Equiv.cast h).trans e) a) a := by
  cases h
  exact he a

section Transport

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)

omit [NeZero m] in
private theorem observeFiber_tape_heq
    (p : Path branch root (h + 1))
    (outside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (sources : SourceChildKernel.Sources (m := m) (t := t) designated)
    (x : CleanPhysicalReplay.Sample (t := t) rows repeats p clauses designated)
    (hs : sources = SourcePhysicalTapeLaw.sourceTag rows repeats p clauses designated x)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder) :
    HEq (SourcePhysicalTapeLaw.observeFiber rows repeats p outside placeholder clauses designated
        sources (external, SourceQuestionRawSwap.raw rows clauses designated x)).2
      (WholeCutSampler.collapse rows repeats p
        (CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated
          x external)) := by
  cases hs
  rfl

omit [NeZero m] in
private theorem collapsedRightTape_heq
    {p q : Path branch root (h + 1)} (hp : p = q)
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (placeholder otherPlaceholder : Slots branch (h + 1) → Fin t → MixedSupport.Slot)
    (x : CleanPhysicalReplay.Sample (t := t) rows repeats p clauses designated)
    (y : CleanPhysicalReplay.Sample (t := t) rows repeats q clauses designated)
    (hx : HEq x y)
    (external : CleanPhysicalReplay.Exterior rows repeats p outside placeholder)
    (other : CleanPhysicalReplay.Exterior rows repeats q otherOutside otherPlaceholder)
    (hext : HEq external other)
    (hslots : CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated x =
      CleanPhysicalCanonicalQuery.rightSlots rows repeats q otherOutside clauses designated y) :
    HEq (WholeCutSampler.collapse rows repeats p
        (CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated x)
        (CleanPhysicalReplay.rightTape rows repeats p outside placeholder clauses designated
          x external))
      (WholeCutSampler.collapse rows repeats q
        (CleanPhysicalCanonicalQuery.rightSlots rows repeats q otherOutside clauses designated y)
        (CleanPhysicalReplay.rightTape rows repeats q otherOutside otherPlaceholder clauses designated
          y other)) := by
  cases hp
  have hxy : x = y := eq_of_heq hx
  cases hxy
  exact SourcePhysicalExteriorReplay.collapsedTape_heq rows repeats p
    outside otherOutside placeholder otherPlaceholder
    (CleanPhysicalReplay.rightInside rows repeats p clauses designated x)
    hslots external other hext (CleanPhysicalReplay.rightBlocks rows repeats p clauses designated x)

private theorem joinedExterior_heq
    (p : Path branch root (h + 1))
    (inside : PreliminarySampler.Questions branch (h + 1) t m)
    (external : SourceQuestionCutSplit.OutsideQuestions p t m)
    (exterior : SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external) :
    HEq (@Equiv.toFun
      (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p external)
      (SourcePhysicalExteriorSwap.ActualExterior clauses rows repeats p
        (SourceQuestionCutSplit.join p inside external))
      (SourcePhysicalSourceSwap.joinedExterior clauses rows repeats p inside external) exterior)
      exterior := by
  exact cast_trans_toFun_heq
    (congrArg (SourcePhysicalExteriorSwap.CanonicalExterior clauses rows repeats p)
      (SourcePhysicalSourceSwap.outside_join p inside external).symm)
    (SourcePhysicalExteriorSwap.fromCanonical clauses rows repeats p
      (SourceQuestionCutSplit.join p inside external))
    (SourcePhysicalExteriorSwap.fromCanonical_heq clauses rows repeats p
      (SourceQuestionCutSplit.join p inside external)) exterior

end Transport

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)
  (sample : FixedStoppedNativeLaw.Sample parameters i j hij input)

local notation "R" => FixedRows.rows parameters.plan
local notation "T" => FixedRows.repeats parameters.plan
local notation "C" => clauses input
local notation "D" => designated parameters i
local notation "hu" => Nat.succ_le_of_lt j.isLt
local notation "P" => physicalSample parameters i j hij input sample
local notation "K" => innerTag parameters i j hij input sample
local notation "S" => FixedStoppedNativeLaw.setup parameters i j hij input (Sigma.fst sample)

private theorem exterior_heq : HEq (S).exterior P.2.1.2.1 := by
  have hclean : HEq (S).exterior sample.1.2.2.2.2 := by
    have hfilled : HEq
        (StoppedCleanGeometry.filledExteriorEquiv parameters input
          (FixedStoppedDecoderContext.upperPath parameters i j sample.1.1)
          (FixedStoppedDecoderContext.lowerPath parameters i j hij sample.1.1)
          sample.1.2.1 sample.1.2.2.2.2) sample.1.2.2.2.2 := cast_heq _ _
    exact (cast_heq _ _).trans hfilled
  have hphysical : HEq P.2.1.2.1 sample.1.2.2.2.2 := by
    exact joinedExterior_heq R T C
      (path parameters i j hij input sample)
      (SourceQuestionRawSwap.insideQuestions R C D (childSample parameters i j hij input sample))
      sample.1.2.1 sample.1.2.2.2.2
  exact hclean.trans hphysical.symm

theorem physicalRead_tape_heq :
    HEq (physicalRead parameters i j hij input sample).2
      (CleanPhysicalDecoderLaw.rightWholeTape S sample.2) := by
  have hphysical := observeFiber_tape_heq R T C D
    (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots C P.1)
    (SourceProjectedTag.originalSlots C
      (StoppedProjectedExperiment.cutQuestions R hu hij P.1
        (StoppedProjectedExperiment.baseTag R P.2.1.1)))
    (StoppedProjectedExperiment.physicalSources R hu hij D P.1 P.2.1.1)
    (childSample parameters i j hij input sample)
    (FixedStoppedNativeProjection.physicalSources_eq parameters i j hij input sample)
    P.2.1.2.1
  have hchild : HEq sample.2 (childSample parameters i j hij input sample) :=
    (cast_heq _ _).symm
  have hclean := collapsedRightTape_heq R T C D
    (FixedStoppedNativeLaw.path_eq parameters i j hij input sample.1)
    (S).outside (StoppedProjectedExperiment.nativeSlots C P.1)
    (S).placeholder
    (SourceProjectedTag.originalSlots C
      (StoppedProjectedExperiment.cutQuestions R hu hij P.1
        (StoppedProjectedExperiment.baseTag R P.2.1.1)))
    sample.2 (childSample parameters i j hij input sample) hchild
    (S).exterior P.2.1.2.1 (exterior_heq parameters i j hij input sample)
    ((FixedStoppedNativeProjection.rightSlots_eq parameters i j hij input sample).trans
      (FixedStoppedNativeProjection.physicalRightSlots_eq parameters i j hij input sample))
  exact hphysical.trans hclean.symm

theorem experimentTape_heq_oai :
    HEq (experimentRead parameters i j hij input sample).2
      (CleanPhysicalDecoderLaw.uncastTape (CleanNativeReplay.rightSlots S sample.2)
        (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
        (CleanPhysicalDecoderLaw.lower S) (S).cut
        (CleanDecoderContext.lowerHeight
          (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
          (FixedStoppedDecoderContext.lowerIndex parameters i j hij input sample.1))
        (CleanPhysicalDecoderLaw.rightWholeTape S sample.2)) := by
  have hphysical := StoppedCleanOwnInputGeometry.pathTapeEquiv_heq R T
    (StoppedProjectedExperiment.projectedSlots C R hu hij D P.1 K)
    (StoppedProjectedExperiment.fullPath_spec R hu hij P.1 K).symm
    (physicalRead parameters i j hij input sample).2
  have hclean := StoppedCleanOwnInputGeometry.uncastTape_heq R T
    (CleanNativeReplay.rightSlots S sample.2)
    (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
    (CleanPhysicalDecoderLaw.lower S) (S).cut
    (CleanDecoderContext.lowerHeight
      (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
      (FixedStoppedDecoderContext.lowerIndex parameters i j hij input sample.1))
    (CleanPhysicalDecoderLaw.rightWholeTape S sample.2)
  exact hphysical.trans ((physicalRead_tape_heq parameters i j hij input sample).trans hclean.symm)

end
end PerfectCompleteness.FixedStoppedNativeTape

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedNativeTape.experimentTape_heq_oai := @OAI.PerfectCompleteness.FixedStoppedNativeTape.experimentTape_heq_oai
