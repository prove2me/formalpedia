-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:27.233229+00:00
-- url     : https://prove2.me/submissions/2fd9f858-8781-4fac-8b9d-deefed3eeff7

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
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedNativeTape_experimentTape_heq

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_WholeArrayInteriorExteriorLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.WholeArrayInteriorExterior

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays WholeArraySampler
open WholeArraySubtreeSplit
open scoped Classical

noncomputable section

variable {branch : Nat → Nat} {N n m t : Nat}

theorem upperNode_path_heq (p : Path branch N (n + 1)) :
    HEq (Nodes.path (upperNode p)) p :=
  (Sigma.mk.inj (upperNode_spec p)).2

end
end PerfectCompleteness.WholeArrayInteriorExterior


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_StoppedCleanOwnInputGeometry
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype
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

variable (slots target : Slots branch n → Fin t → MixedSupport.Slot)
  (hslots : slots = target) (upper lower otherLower : Nodes branch n)
  (hlower : lower = otherLower)
  (cut : OwnInputReference.Cut upper lower)
  (otherCut : OwnInputReference.Cut upper otherLower) (hcut : HEq cut otherCut)
  (W : Submodule F2 (Block rows upper))
  (tape : WholeArraySampler.Tape rows repeats
    (WholeArrayInteriorOwnInputLaw.fullPath upper lower cut) slots)
  (otherTape : WholeArraySampler.Tape rows repeats
    (WholeArrayInteriorOwnInputLaw.fullPath upper otherLower otherCut) target)
  (htape : HEq tape otherTape)

include hslots hlower hcut htape

theorem visibleRead_heq :
    HEq (WholeArrayInteriorOwnInputLaw.exposedRead rows repeats slots upper lower cut W tape).2
      (WholeArrayInteriorOwnInputLaw.exposedRead rows repeats target upper otherLower
        otherCut W otherTape).2 := by
  cases hslots
  cases hlower
  have hc : cut = otherCut := eq_of_heq hcut
  cases hc
  have ht : tape = otherTape := eq_of_heq htape
  cases ht
  rfl

end
end PerfectCompleteness.StoppedCleanOwnInputGeometry

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Repetition_StoppedCleanCutEquality
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.StoppedCleanCutEquality

open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat}

theorem append_left_injective {N M K : Nat} (pref : Path branch N M) :
    Function.Injective (fun suff : Path branch M K => pref.append suff) := by
  induction pref with
  | refl _ => intro a b hab; exact hab
  | step child pref ih =>
      intro a b hab
      apply ih
      change Path.step child (pref.append a) = Path.step child (pref.append b) at hab
      injection hab

theorem cut_eq_of_path_eq {N : Nat} {upper lower : Nodes branch N}
    (left right : OwnInputReference.Cut upper lower) (hpath : left.path = right.path) :
    left = right := by
  cases left
  cases right
  cases hpath
  rfl

theorem cut_heq_of_fullPath_heq {N : Nat} {upper lower₁ lower₂ : Nodes branch N}
    (hlower : lower₁ = lower₂)
    (left : OwnInputReference.Cut upper lower₁) (right : OwnInputReference.Cut upper lower₂)
    (hpath : HEq (WholeArrayInteriorOwnInputLaw.fullPath upper lower₁ left)
      (WholeArrayInteriorOwnInputLaw.fullPath upper lower₂ right)) : HEq left right := by
  cases hlower
  apply heq_of_eq
  apply cut_eq_of_path_eq
  exact append_left_injective (Nodes.path upper) (eq_of_heq hpath)

theorem cutOfBelow_heq_selectedCut {N i j : Nat}
    (p : Path branch N (j + 1)) (q : Path branch (j + 1) (i + 1)) (hij : i < j) :
    HEq (StoppedOwnInputGeometry.cutOfBelow (StoppedProjectedExperiment.below_append hij p q))
      (StoppedCleanGeometry.cut p q hij) := by
  refine cut_heq_of_fullPath_heq (StoppedCleanGeometry.lowerNode_descendant p q hij).symm
    _ _ ?_
  have hphysical : HEq
      (WholeArrayInteriorOwnInputLaw.fullPath (WholeArrayInteriorExterior.upperNode p)
        (WholeArrayInteriorExterior.upperNode (p.append q))
        (StoppedOwnInputGeometry.cutOfBelow (StoppedProjectedExperiment.below_append hij p q)))
      (p.append q) := by
    rw [StoppedOwnInputGeometry.fullPath_cutOfBelow]
    exact WholeArrayInteriorExterior.upperNode_path_heq (p.append q)
  exact hphysical.trans ((Sigma.mk.inj (StoppedCleanGeometry.fullPath_spec p q hij)).2.symm)

variable {n i j t m : Nat} (rows : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (o : StoppedProjectedExperiment.Outer
    (branch := branch) (n := n) (j := j) (t := t) (m := m))
  (k : StoppedProjectedExperiment.Inner
    (branch := branch) (n := n) (i := i) (j := j) (t := t) rows)

theorem stopped_lower_eq :
    StoppedProjectedExperiment.lower rows hupper hij o k =
      HierarchicalLeftDecoder.LowerNode (StoppedProjectedExperiment.upper hupper o) (i + 1)
        (StoppedCleanGeometry.descendant (StoppedProjectedExperiment.upperPath hupper o)
          (StoppedProjectedExperiment.lowerPath rows hij k) hij) :=
  (StoppedCleanGeometry.lowerNode_descendant (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedExperiment.lowerPath rows hij k) hij).symm

theorem stopped_cut_heq :
    HEq (StoppedProjectedExperiment.cut rows hupper hij o k)
      (StoppedCleanGeometry.cut (StoppedProjectedExperiment.upperPath hupper o)
        (StoppedProjectedExperiment.lowerPath rows hij k) hij) :=
  cutOfBelow_heq_selectedCut (StoppedProjectedExperiment.upperPath hupper o)
    (StoppedProjectedExperiment.lowerPath rows hij k) hij

end PerfectCompleteness.StoppedCleanCutEquality

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_FixedStoppedNativeTape
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty
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

theorem visible_heq_oai :
    HEq (rawRead parameters i j hij input sample).2.2.2.2
      (CleanPhysicalProjectedMeeting.visible S
        (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
        sample.2) :=
  StoppedCleanOwnInputGeometry.visibleRead_heq R T
    (StoppedProjectedExperiment.projectedSlots C R hu hij D P.1 K)
    (CleanNativeReplay.rightSlots S sample.2)
    (FixedStoppedNativeProjection.rightSlots_eq parameters i j hij input sample).symm
    (StoppedProjectedExperiment.upper hu P.1)
    (StoppedProjectedExperiment.lower R hu hij P.1 K) (CleanPhysicalDecoderLaw.lower S)
    (StoppedCleanCutEquality.stopped_lower_eq R hu hij P.1 K)
    (StoppedProjectedExperiment.cut R hu hij P.1 K) (S).cut
    (StoppedCleanCutEquality.stopped_cut_heq R hu hij P.1 K)
    (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1))
    (experimentRead parameters i j hij input sample).2 _
    (experimentTape_heq parameters i j hij input sample)

end
end PerfectCompleteness.FixedStoppedNativeTape

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq_oai := @OAI.PerfectCompleteness.FixedStoppedNativeTape.visible_heq_oai
