-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedNativeProjection.projection_heq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:23.950204+00:00
-- url     : https://prove2.me/submissions/e906f195-1de0-4fcb-8e58-ec51b557c1fa

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionAssembly
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CutProjectionGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeDecidableEq
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_StoppedProjectedArrays
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedProjectedArrays

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private theorem sourceProjection_heq
    {branch : Nat → Nat} {i t v m : Nat}
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch i) → Slots branch i)
    (q : PreliminarySampler.Questions branch (i + 1) t m)
    (positions : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i))
    (leaf : Slots branch (i + 1)) (a : Fin t) :
    HEq (SourceProjectedTag.projection clauses designated q positions flags leaf a)
      (SourceChildKernel.projection clauses designated leaf.1
        (SourceQuestionKernelJoint.sources designated q positions leaf.1)
        (flags leaf.1) leaf.2 a) := by
  unfold SourceProjectedTag.projection
  dsimp only [id]
  exact mpr_heq _ _

private theorem fillProjection_heq
    {branch : Nat → Nat} {n h t : Nat} (p : Path branch n h)
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    {left left' right right' : Slots branch h → Fin t → MixedSupport.Slot}
    (hl : left = left') (hr : right = right')
    (q : ∀ s a, MixedSupport.Projection (left s a) (right s a))
    (q' : ∀ s a, MixedSupport.Projection (left' s a) (right' s a))
    (hq : ∀ s a, HEq (q s a) (q' s a)) (leaf : Slots branch n) (a : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q leaf a)
      (CutProjectionAssembly.fillProjection p outside left' right' q' leaf a) := by
  cases hl
  cases hr
  have he : q = q' := funext (fun s => funext (fun a => eq_of_heq (hq s a)))
  cases he
  rfl

variable {branch : Nat → Nat} {n i j t v m : Nat}
  (clauses : Fin m → SourceClause.NormalizedClause v)
  (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (designated : Fin (branch i) → Slots branch i)

theorem projection_heq
    (o : StoppedProjectedExperiment.Outer
      (branch := branch) (n := n) (j := j) (t := t) (m := m))
    (base : StoppedProjectedExperiment.PhysicalBase
      (branch := branch) (n := n) (i := i) (j := j) (t := t) rows)
    (flags : SourceProjectedTag.Flags (branch := branch) (n := i))
    (leaf : Slots branch n) (a : Fin t) :
    HEq (StoppedProjectedExperiment.projection clauses rows hupper hij designated o
        (StoppedProjectedExperiment.withFlags rows base flags) leaf a)
      (SourcePhysicalTapeLaw.fullProjection
        (StoppedProjectedExperiment.stoppedPath rows hupper hij o
          (StoppedProjectedExperiment.baseTag rows base))
        (StoppedProjectedExperiment.nativeSlots clauses o) clauses designated
        (StoppedProjectedExperiment.physicalSources rows hupper hij designated o base, flags)
        leaf a) := by
  unfold StoppedProjectedExperiment.projection
  apply (CutProjectionAssembly.castProjection_heq _ _ _).trans
  exact fillProjection_heq
    (StoppedProjectedExperiment.stoppedPath rows hupper hij o
      (StoppedProjectedExperiment.baseTag rows base))
    (StoppedProjectedExperiment.nativeSlots clauses o)
    (SourceProjectedTag.parentLeftSlots_sources clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows base)) base.2.1).symm
    rfl _ _
    (sourceProjection_heq clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij o
        (StoppedProjectedExperiment.baseTag rows base)) base.2.1 flags) leaf a

end
end PerfectCompleteness.StoppedProjectedArrays

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
theorem leftSlots_sourceSampleEquiv (hp : p = q)
    (x : SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated) :
    CleanPhysicalCanonicalQuery.leftSlots rows repeats p outside clauses designated x =
      CleanPhysicalCanonicalQuery.leftSlots rows repeats q outside clauses designated
        (FixedStoppedNativeLaw.sourceSampleEquiv rows repeats clauses designated hp x) := by
  cases hp
  rfl

omit [NeZero m] in
theorem projection_sourceSampleEquiv_heq (hp : p = q)
    (x : SourceChildKernel.Sample (C := WholeCutCalls.Index rows repeats p) (t := t)
      rows clauses designated) (leaf : Slots branch root) (coordinate : Fin t) :
    HEq (CleanPhysicalCanonicalQuery.projection rows repeats p outside clauses designated x
      leaf coordinate)
      (CleanPhysicalCanonicalQuery.projection rows repeats q outside clauses designated
        (FixedStoppedNativeLaw.sourceSampleEquiv rows repeats clauses designated hp x)
        leaf coordinate) := by
  cases hp
  rfl

end PathTransport

theorem fillProjection_outsidePresentation_heq
    {branch : Nat → Nat} {root h t : Nat} (p : Path branch root h)
    (outside otherOutside : Slots branch root → Fin t → MixedSupport.Slot)
    (left right : Slots branch h → Fin t → MixedSupport.Slot)
    (q : ∀ s k, MixedSupport.Projection (left s k) (right s k))
    (hfillLeft : CutSlotAssembly.fill p outside left =
      CutSlotAssembly.fill p otherOutside left) (leaf : Slots branch root) (a : Fin t) :
    HEq (CutProjectionAssembly.fillProjection p outside left right q leaf a)
      (CutProjectionAssembly.fillProjection p otherOutside left right q leaf a) := by
  by_cases hin : leaf ∈ Set.range p.slotEmbedding
  · obtain ⟨s, rfl⟩ := hin
    exact (CutProjectionAssembly.fillProjection_at_cut p outside left right q s a).trans
      (CutProjectionAssembly.fillProjection_at_cut p otherOutside left right q s a).symm
  · have hkeep (s u : MixedSupport.Slot) (hsu : s = u) :
        HEq (MixedSupport.Projection.keep s) (MixedSupport.Projection.keep u) := by
      cases hsu
      rfl
    exact (CutProjectionGeometry.fillProjection_outside p outside left right q leaf hin a).trans
      ((hkeep _ _ (congrFun (congrFun hfillLeft leaf) a)).trans
        (CutProjectionGeometry.fillProjection_outside p otherOutside left right q leaf hin a).symm)

private theorem fullProjection_sources_heq
    {branch : Nat → Nat} {root h t v m : Nat} [NeZero m]
    (p : Path branch root (h + 1))
    (outside : Slots branch root → Fin t → MixedSupport.Slot)
    (clauses : Fin m → SourceClause.NormalizedClause v)
    (designated : Fin (branch h) → Slots branch h)
    {sources other : SourceChildKernel.Sources (m := m) (t := t) designated}
    (hsources : sources = other) (flags : Fin (branch h) → Bool)
    (leaf : Slots branch root) (a : Fin t) :
    HEq (SourcePhysicalTapeLaw.fullProjection p outside clauses designated (sources, flags) leaf a)
      (SourcePhysicalTapeLaw.fullProjection p outside clauses designated (other, flags) leaf a) := by
  cases hsources
  rfl

private theorem projection_function_heq
    {branch : Nat → Nat} {n t : Nat}
    {left left' right right' : Slots branch n → Fin t → MixedSupport.Slot}
    (hl : left = left') (hr : right = right')
    (p : ∀ leaf a, MixedSupport.Projection (left leaf a) (right leaf a))
    (q : ∀ leaf a, MixedSupport.Projection (left' leaf a) (right' leaf a))
    (hpq : ∀ leaf a, HEq (p leaf a) (q leaf a)) : HEq p q := by
  cases hl
  cases hr
  exact heq_of_eq (funext (fun leaf => funext (fun a => eq_of_heq (hpq leaf a))))

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

theorem leftSlots_eq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    CleanNativeReplay.leftSlots (FixedStoppedNativeLaw.setup parameters i j hij input sample.1)
        sample.2 =
      StoppedProjectedExperiment.nativeSlots (clauses input)
        (physicalSample parameters i j hij input sample).1 := by
  have hp := leftSlots_sourceSampleEquiv (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan)
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside
    (clauses input) (designated parameters i)
    (FixedStoppedNativeLaw.path_eq parameters i j hij input sample.1) sample.2
  refine hp.trans ((fill_outside_eq parameters i j hij input sample _).trans ?_)
  exact (congrArg (SourcePhysicalTapeLaw.nativeSlots (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1) (clauses input) (designated parameters i))
    (physicalSources_eq parameters i j hij input sample)).symm.trans
      (StoppedProjectedArrays.nativeSlots_eq (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (physicalSample parameters i j hij input sample).2.1.1)

theorem projection_apply_heq (sample : FixedStoppedNativeLaw.Sample parameters i j hij input)
    (leaf : Slots (FixedParameters.branch parameters) parameters.plan.depth)
    (a : Fin (FixedRows.sourceLength parameters.plan hδ)) :
    HEq (CleanPhysicalDecoderLaw.physicalProjection
      (FixedStoppedNativeLaw.setup parameters i j hij input sample.1) sample.2 leaf a)
      (StoppedProjectedExperiment.projection (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (innerTag parameters i j hij input sample) leaf a) := by
  have hp := projection_sourceSampleEquiv_heq (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan)
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside
    (clauses input) (designated parameters i)
    (FixedStoppedNativeLaw.path_eq parameters i j hij input sample.1) sample.2 leaf a
  have hout := fillProjection_outsidePresentation_heq (path parameters i j hij input sample)
    (FixedStoppedNativeLaw.setup parameters i j hij input sample.1).outside
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1)
    (CleanPhysicalReplay.leftInside (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (path parameters i j hij input sample) (clauses input) (designated parameters i)
      (childSample parameters i j hij input sample))
    (CleanPhysicalReplay.rightInside (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (path parameters i j hij input sample) (clauses input) (designated parameters i)
      (childSample parameters i j hij input sample))
    (SourceChildKernel.parentProjection (FixedRows.rows parameters.plan) (clauses input)
      (designated parameters i) (sources parameters i j hij input sample)
      (fun child => ((childSample parameters i j hij input sample) child).2.2))
    (fill_outside_eq parameters i j hij input sample _) leaf a
  have hs := fullProjection_sources_heq (path parameters i j hij input sample)
    (StoppedProjectedExperiment.nativeSlots (clauses input)
      (physicalSample parameters i j hij input sample).1) (clauses input) (designated parameters i)
    (physicalSources_eq parameters i j hij input sample).symm
    (flags parameters i j hij input sample) leaf a
  have hphysical := StoppedProjectedArrays.projection_heq (clauses input)
    (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
    (physicalSample parameters i j hij input sample).1
    (physicalSample parameters i j hij input sample).2.1.1
    (flags parameters i j hij input sample) leaf a
  exact hp.trans (hout.trans (hs.trans hphysical.symm))

theorem projection_heq_oai (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    HEq (CleanPhysicalDecoderLaw.physicalProjection
      (FixedStoppedNativeLaw.setup parameters i j hij input sample.1) sample.2)
      (StoppedProjectedExperiment.projection (clauses input) (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij (designated parameters i)
        (physicalSample parameters i j hij input sample).1
        (innerTag parameters i j hij input sample)) :=
  projection_function_heq (leftSlots_eq parameters i j hij input sample)
    (rightSlots_eq parameters i j hij input sample) _ _
    (projection_apply_heq parameters i j hij input sample)

end
end PerfectCompleteness.FixedStoppedNativeProjection

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedNativeProjection.projection_heq_oai := @OAI.PerfectCompleteness.FixedStoppedNativeProjection.projection_heq_oai
