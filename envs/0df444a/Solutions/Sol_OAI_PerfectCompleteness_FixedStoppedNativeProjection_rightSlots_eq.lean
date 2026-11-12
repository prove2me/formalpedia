-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedNativeProjection.rightSlots_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:25.03624+00:00
-- url     : https://prove2.me/submissions/2ee8e6c1-74eb-4a08-9084-011e66bdc069

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

theorem fill_eq (questions : PreliminarySampler.Questions branch root t m)
    (inside : Slots branch (h + 1) → Fin t → MixedSupport.Slot) :
    CutSlotAssembly.fill p (sourceSlots clauses (PreliminarySampler.endpoints questions)) inside =
      CutSlotAssembly.fill p
        (canonicalSlots clauses p (SourceQuestionCutSplit.outside p questions)) inside := by
  funext leaf
  by_cases hleaf : leaf ∈ Set.range p.slotEmbedding
  · obtain ⟨s, rfl⟩ := hleaf
    rw [CutSlotAssembly.fill_at_cut, CutSlotAssembly.fill_at_cut]
  · rw [CutSlotAssembly.fill_outside p _ _ leaf hleaf,
      CutSlotAssembly.fill_outside p _ _ leaf hleaf]
    exact (canonicalSlots_outside clauses p
      (SourceQuestionCutSplit.outside p questions) ⟨leaf, hleaf⟩).symm

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

section PathTransport

variable {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
  (rows repeats : Nat → Nat)
  (outside : Slots branch root → Fin t → MixedSupport.Slot)
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch h) → Slots branch h)
  {p q : Path branch root (h + 1)}

omit [NeZero m] in
theorem rightSlots_sourceSampleEquiv (hp : p = q)
    (x : SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated) :
    CleanPhysicalCanonicalQuery.rightSlots rows repeats p outside clauses designated x =
      CleanPhysicalCanonicalQuery.rightSlots rows repeats q outside clauses designated
        (FixedStoppedNativeLaw.sourceSampleEquiv rows repeats clauses designated hp x) := by
  cases hp
  rfl

end PathTransport

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

theorem outside_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside =
      SourcePhysicalExteriorSwap.canonicalSlots (clauses input) (path parameters i j hij input sample)
        (SourceQuestionCutSplit.outside (path parameters i j hij input sample)
          (originalQuestions parameters i j hij input sample)) := by
  change SourcePhysicalExteriorSwap.canonicalSlots (clauses input)
      (path parameters i j hij input sample) sample.1.2.1 =
    SourcePhysicalExteriorSwap.canonicalSlots (clauses input) (path parameters i j hij input sample)
      (SourceQuestionCutSplit.outside (path parameters i j hij input sample)
        (SourceQuestionCutSplit.join (path parameters i j hij input sample) _ sample.1.2.1))
  exact (congrArg (SourcePhysicalExteriorSwap.canonicalSlots (clauses input)
      (path parameters i j hij input sample))
    (SourcePhysicalSourceSwap.outside_join (path parameters i j hij input sample)
      (SourceQuestionRawSwap.insideQuestions (FixedRows.rows parameters.plan)
        (clauses input) (designated parameters i) (childSample parameters i j hij input sample))
      sample.1.2.1)).symm

theorem fill_outside_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input)
    (inside : Slots (FixedParameters.branch parameters) (i.val + 1) →
      Fin (FixedRows.sourceLength parameters.plan hδ) → MixedSupport.Slot) :
    CutSlotAssembly.fill (path parameters i j hij input sample)
        (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside inside =
      CutSlotAssembly.fill (path parameters i j hij input sample)
        (StoppedProjectedExperiment.nativeSlots (clauses input)
          (physicalSample parameters i j hij input sample).1) inside := by
  rw [outside_eq]
  exact (SourcePhysicalExteriorSwap.fill_eq (clauses input)
    (path parameters i j hij input sample) (originalQuestions parameters i j hij input sample)
    inside).symm

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

theorem rightSlots_eq_oai (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    CleanNativeReplay.rightSlots (FixedStoppedNativeLaw.setup parameters i j hij input sample.1)
        sample.2 =
      StoppedProjectedExperiment.projectedSlots (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (innerTag parameters i j hij input sample) := by
  have hp := rightSlots_sourceSampleEquiv (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan)
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside
    (clauses input) (designated parameters i)
    (FixedStoppedNativeLaw.path_eq parameters i j hij input sample.1) sample.2
  refine hp.trans ((fill_outside_eq parameters i j hij input sample _).trans ?_)
  exact (physicalRightSlots_eq parameters i j hij input sample).symm

end
end PerfectCompleteness.FixedStoppedNativeProjection

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedNativeProjection.rightSlots_eq_oai := @OAI.PerfectCompleteness.FixedStoppedNativeProjection.rightSlots_eq_oai
