-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rawPrediction_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:24:57.755953+00:00
-- url     : https://prove2.me/submissions/ff715fa6-5194-4ccd-a686-6c5618bd3c09

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ClauseSupportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyDomainFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.entryWords_length _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_cons _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_length _root_.OAI.PerfectCompleteness.KeyMetadataEncoding.metadataWords_nil _root_.OAI.PerfectCompleteness.NormalizedSourceInput.signs_eq _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.actualProjection_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_decode _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.clauseAnswerEquiv_symm_val _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_apply _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.leftEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceGame.decodeLabel_encodeLabel _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ClauseSupport

open SourceClause

variable {C C' D E Y Z : Type*}

theorem unprojected_clause_key_eq {signs : Triple} (f : C → Answer signs → Y)
    (context : C' → C) (hcontext : Function.Surjective context)
    (occurrence : Nat) (variableIDs : Fin 3 → Nat) :
    clauseKey occurrence variableIDs (pull f context id) = clauseKey occurrence variableIDs f := by
  simp only [clauseKey, unprojected_mode_eq f context hcontext]

theorem unprojected_bit_key_eq (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context) (variableID : Nat) :
    bitKey variableID (pull f context id) = bitKey variableID f := by
  classical
  simp only [bitKey, unused_pull_iff f context id hcontext Function.surjective_id]

theorem projected_key_eq {signs : Triple} (f : C → Bool → Y)
    (context : C' → C) (hcontext : Function.Surjective context)
    (occurrence : Nat) (variableIDs : Fin 3 → Nat) (i : Fin 3) :
    clauseKey occurrence variableIDs (pull f context (coordinate (signs := signs) i)) =
      bitKey (variableIDs i) f := by
  classical
  have hu := projected_unused_iff (signs := signs) f context hcontext i
  by_cases hf : Unused f
  · simp [clauseKey, clauseMode_unused _ (hu.2 hf), bitKey, hf]
  · have hp : ¬ Unused (pull f context (coordinate (signs := signs) i)) :=
      fun h => hf (hu.1 h)
    rw [clauseKey, clauseMode_bit _ hp i (projected_reducible f context i)]
    simp [bitKey, hf]

end PerfectCompleteness.ClauseSupport

end

section

namespace PerfectCompleteness.MixedSupport

open ClauseSupport

variable {I C C' Y : Type*}

variable [DecidableEq I]

theorem localKey_projection {s t : Slot} (p : Projection s t)
    (f : C → t.Domain → Y) (context : C' → C)
    (hcontext : Function.Surjective context) :
    localKey s (pull f context p.map) = localKey t f := by
  cases p with
  | keep s =>
    cases s with
    | clause occurrence variableIDs signs =>
      exact unprojected_clause_key_eq f context hcontext occurrence variableIDs
    | bit variableID => exact unprojected_bit_key_eq f context hcontext variableID
  | select occurrence variableIDs signs i =>
    exact projected_key_eq f context hcontext occurrence variableIDs i

theorem keyFields_projection {slots projected : I → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    keyFields slots (f ∘ projectionMap p) = keyFields projected f := by
  funext i
  unfold keyFields
  rw [sectionFunction_pullback]
  exact localKey_projection (p i) (sectionFunction projected f i)
    (projectionMap p) (projectionMap_surjective p)

theorem retainedKeys_projection {n : Nat} {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    retainedKeys slots (f ∘ projectionMap p) = retainedKeys projected f := by
  simp only [retainedKeys, keyFields_projection]

end PerfectCompleteness.MixedSupport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_CanonicalKeys
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalKeys

open ClauseSupport MixedSupport

variable {n : Nat} {Y : Type*}

theorem key_projection (side : Side) {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y) :
    key side slots (f ∘ projectionMap p) = key side projected f := by
  simp only [key, retainedKeys_projection, partition_projection]

theorem restore_projection {slots projected : Fin n → Slot}
    (p : ∀ i, Projection (slots i) (projected i)) (f : Assignment projected → Y)
    (P : Label slots (f ∘ projectionMap p)) :
    restore slots (f ∘ projectionMap p) P =
      restore projected f (transportLabel p f P) := by
  exact ReducedPartition.output_eq_of_shared_part
    (projectionMap p) (reduction slots (f ∘ projectionMap p)) (reduction projected f)
    (f ∘ projectionMap p) f (reduction_projection p f) (fun _ => rfl)
    (constantOnFibers projected f) P (transportLabel p f P) rfl

end PerfectCompleteness.CanonicalKeys

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuotientTableAgreementLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.KeyStrategy

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys

variable {n : Nat} {Y Z : Type*}

theorem label_val_eq_of_key_eq (σ : Strategy n) (side side' : Side)
    (slots projected : Fin n → Slot) (f : Assignment slots → Y)
    (g : Assignment projected → Z) (hkey : key side slots f = key side' projected g) :
    (label σ side slots f).val = (label σ side' projected g).val := by
  have hk : queryKey side slots f = queryKey side' projected g := Subtype.ext hkey
  exact congrArg (fun k : NonemptyKey n => (σ k).val) hk

theorem response_postcomp_injective (σ : Strategy n) (side : Side)
    (slots : Fin n → Slot) (f : Assignment slots → Y) (e : Y → Z)
    (he : Function.Injective e) :
    response σ side slots (e ∘ f) = e (response σ side slots f) := by
  let hkernel : ∀ x x', f x = f x' ↔ (e ∘ f) x = (e ∘ f) x' :=
    fun _ _ => ⟨fun h => congrArg e h, fun h => he h⟩
  have hlabel : label σ side slots (e ∘ f) =
      transportKernel slots f (e ∘ f) hkernel (label σ side slots f) := by
    apply Subtype.ext
    exact label_val_eq_of_key_eq σ side side slots slots (e ∘ f) f
      (key_postcomp_injective side slots f e he)
  unfold response
  rw [hlabel]
  exact restore_transportKernel slots f (e ∘ f) hkernel e (fun _ => rfl)
    (label σ side slots f)

theorem response_projection (σ : Strategy n) (side : Side)
    {slots projected : Fin n → Slot} (p : ∀ i, Projection (slots i) (projected i))
    (f : Assignment projected → Y) :
    response σ side slots (f ∘ projectionMap p) = response σ side projected f := by
  have hlabel : transportLabel p f (label σ side slots (f ∘ projectionMap p)) =
      label σ side projected f := by
    apply Subtype.ext
    exact label_val_eq_of_key_eq σ side side slots projected (f ∘ projectionMap p) f
      (key_projection side p f)
  unfold response
  rw [restore_projection, hlabel]

end
end PerfectCompleteness.KeyStrategy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_TreeCanonical
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.TreeCanonical

open MixedSupport TreeSourceSpaces

noncomputable section

variable {branch : Nat → Nat} {n t : Nat} {Y : Type*}

theorem assignmentEquiv_projection
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k)) (x : Domain slots) :
    assignmentEquiv projected (sourceProjection p x) =
      MixedSupport.projectionMap (numberedProjection p) (assignmentEquiv slots x) := rfl

theorem assignmentEquiv_symm_projection
    {slots projected : RecursiveSpaces.Slots branch n → Fin t → Slot}
    (p : ∀ s k, Projection (slots s k) (projected s k))
    (x : MixedSupport.Assignment (numberedSlots slots)) :
    sourceProjection p ((assignmentEquiv slots).symm x) =
      (assignmentEquiv projected).symm (MixedSupport.projectionMap (numberedProjection p) x) := by
  apply (assignmentEquiv projected).injective
  simpa only [Equiv.apply_symm_apply] using
    assignmentEquiv_projection p ((assignmentEquiv slots).symm x)

end

end PerfectCompleteness.TreeCanonical

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_HierarchicalMatrixTable
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalMatrixTable

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (node : Nodes branch n)

theorem nativeRows_matrix (arrays : Arrays slots rows) :
    nativeRows slots node (NodeEmbedding.matrix arrays node) = arrays node := by
  funext i
  change (NodeEmbedding.equiv slots node).symm
    (EvaluationMatrix.rows (NodeEmbedding.RowSpace slots node)
      (EvaluationMatrix.ofRows (NodeEmbedding.RowSpace slots node)
        (NodeEmbedding.embeddedRows arrays node)) i) = arrays node i
  rw [EvaluationMatrix.rows_ofRows]
  exact (NodeEmbedding.equiv slots node).symm_apply_apply _

theorem assemble_original (arrays : Arrays slots rows) :
    assemble slots node (backgroundOf slots node arrays) (NodeEmbedding.matrix arrays node) = arrays := by
  funext j
  by_cases hj : j = node
  · subst j
    rw [assemble_selected, nativeRows_matrix]
  · simp only [assemble, dite_eq_right hj, backgroundOf]

theorem displayed_original (arrays : Arrays slots rows) :
    displayed slots node (backgroundOf slots node arrays) (NodeEmbedding.matrix arrays node) =
      TreeCanonical.numberedFunction slots (fullJoint arrays) := by
  unfold displayed
  rw [assemble_original]

end
end PerfectCompleteness.HierarchicalMatrixTable

end

end OAI
end

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


open PointwiseSpaces RecursiveSpaces DescendantSpaces

universe u

end
end PerfectCompleteness.BucketSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorBucketEvaluationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TensorBucketEvaluation

open scoped BigOperators TensorProduct Classical

noncomputable section

variable {ℓ : Nat} {Ω H : Type*} [AddCommGroup H] [Module F2 H]

theorem tensorOutput_hiddenSum (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H)
    (ω : HiddenBucketBias.HiddenTape W Ω) :
    tensorOutput W q (HiddenBucketBias.hiddenSum W eval ω) =
      ∑ v : HiddenBucketBias.HiddenDirection W, q (eval (ω v)) • v.val.val := by
  change tensorOutputLinear W q
    (∑ v : HiddenBucketBias.HiddenDirection W,
      HiddenBucketBias.directionIn W v ⊗ₜ[F2] eval (ω v)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact tensorOutput_tmul W q (HiddenBucketBias.directionIn W v) (eval (ω v))

theorem evaluate_eq_direction_sum (q : Module.Dual F2 H)
    (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      ∑ v : BucketSampler.Direction ℓ, q (eval (t v)) • v.val := by
  funext i
  rw [BucketSampler.linearMap_evaluate]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v _
  exact mul_comm _ _

theorem evaluate_split (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      visibleOutput W q eval (fun v => t v.val) +
        tensorOutput W q
          (HiddenBucketBias.hiddenSum W eval (fun v => t v.val)) := by
  rw [evaluate_eq_direction_sum, tensorOutput_hiddenSum]
  exact (Fintype.sum_subtype_add_sum_subtype
    (fun v : BucketSampler.Direction ℓ => v.val ∈ W)
    (fun v => q (eval (t v)) • v.val)).symm.trans (add_comm _ _)

theorem evaluate_splitTape (W : Submodule F2 (Fin ℓ → F2))
    (q : Module.Dual F2 H) (eval : Ω → H) (t : BucketSampler.Tape ℓ Ω) :
    (fun i => q (BucketSampler.evaluate ℓ eval t i)) =
      visibleOutput W q eval (HiddenBucketBias.splitTape W Ω t).2 +
        tensorOutput W q
          (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω t).1) :=
  evaluate_split W q eval t

theorem evaluate_apply_split {A : Type*}
    (W : Submodule F2 (Fin ℓ → F2)) (V : Submodule F2 (A → F2))
    (eval : Ω → V) (t : BucketSampler.Tape ℓ Ω) (a : A) :
    (fun i => (BucketSampler.evaluate ℓ eval t i).val a) =
      visibleOutput W (EvaluationMatrix.evaluation V a) eval
        (HiddenBucketBias.splitTape W Ω t).2 +
      tensorOutput W (EvaluationMatrix.evaluation V a)
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω t).1) :=
  evaluate_splitTape W (EvaluationMatrix.evaluation V a) eval t

end

end PerfectCompleteness.TensorBucketEvaluation



namespace PerfectCompleteness.TensorProjectedSlice

noncomputable section

open scoped TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K H H' : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H']
  (i : H' →ₗ[F2] H) (W : Submodule F2 K)

variable (Z : Submodule F2 (Module.Dual F2 H))


variable {ℓ : Nat} (R : Submodule F2 (Fin ℓ → F2))

theorem includedEvaluation_eq_tensorOutputLinear (q : Module.Dual F2 H') :
    R.subtype.comp ((LinearMap.applyₗ (R := F2) q).comp
      (TensorRestriction.tensorEquivHom (W := R) (H := H')).toLinearMap) =
      TensorBucketEvaluation.tensorOutputLinear R q := by
  apply TensorProduct.ext'
  intro w h
  change (TensorRestriction.tensorEquivHom (w ⊗ₜ[F2] h) q : Fin ℓ → F2) =
    TensorBucketEvaluation.tensorOutput R q (w ⊗ₜ[F2] h)
  rw [TensorRestriction.tensorEquivHom_tmul, TensorBucketEvaluation.tensorOutput_tmul]
  rfl

theorem includedEvaluation_eq_tensorOutput (q : Module.Dual F2 H')
    (T : R ⊗[F2] H') :
    (TensorRestriction.tensorEquivHom T q : Fin ℓ → F2) =
      TensorBucketEvaluation.tensorOutput R q T :=
  LinearMap.congr_fun (includedEvaluation_eq_tensorOutputLinear R q) T

theorem prediction_eq_visible_add_tensorOutput
    (X₀ : Module.Dual F2 H →ₗ[F2] (Fin ℓ → F2))
    (T : R ⊗[F2] H') (z : Module.Dual F2 H) (u : Fin ℓ → F2) :
    totalMatrix i R X₀ T z + u =
      (X₀ z + u) + TensorBucketEvaluation.tensorOutput R (i.dualMap z) T := by
  rw [totalMatrix_apply, includedEvaluation_eq_tensorOutput]
  exact add_right_comm _ _ _

end
end PerfectCompleteness.TensorProjectedSlice



namespace PerfectCompleteness.HierarchicalTensorMatrix

noncomputable section

open scoped BigOperators TensorProduct Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (W : Submodule F2 (Block rows upper))

theorem visibleMatrix_apply
    (known : HiddenBucketBias.VisibleDirection W → NodeEmbedding.NodeH slots upper)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :
    visibleMatrix slots upper W known q =
      ∑ v : HiddenBucketBias.VisibleDirection W,
        (q.comp (NodeEmbedding.embed slots upper)) (known v) • v.val.val := by
  simp only [visibleMatrix, LinearMap.sum_apply, LinearMap.smulRight_apply]
  rfl

end
end PerfectCompleteness.HierarchicalTensorMatrix



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorRowAdviceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TensorRowAdvice

noncomputable section

open scoped Classical TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section SelectionCongruence

variable {E K Y : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 E]
  [FiniteDimensional F2 K] [Fintype E] [Fintype K] [Fintype Y]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectedValue_eq_of_advice_eq (f : (E →ₗ[F2] K) → Option Y)
    (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r) (X X₀ : E →ₗ[F2] K)
    (hrow : A.comp X = A.comp X₀) :
    HierarchicalPrediction.selectedValue f r ρ A X =
      HierarchicalPrediction.selectedValue f r ρ A X₀ := by
  exact congrArg
    (fun U : E →ₗ[F2] (Fin r → F2) =>
      if h : ManyGoodRows.GoodRow f r ρ A U then
        some (ManyGoodRows.selectWitness f r ρ A U h).value
      else none) hrow

end SelectionCongruence


variable {K H H' Y : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H'] [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  (i : H' →ₗ[F2] H) (W : Submodule F2 K)
  {r : Nat} (A : ManyGoodRows.RowMap K r) (hW : W ≤ LinearMap.ker A)

include hW

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectedValue_projectMatrix_eq (B : Submodule F2 H)
    (f : (Module.Dual F2 (H ⧸ B) →ₗ[F2] K) → Option Y) (ρ : ℝ)
    (X₀ : Module.Dual F2 H →ₗ[F2] K) (T : W ⊗[F2] H') :
    HierarchicalPrediction.selectedValue f r ρ A
        (MatrixRowQuotient.projectMatrix B (TensorProjectedSlice.totalMatrix i W X₀ T)) =
      HierarchicalPrediction.selectedValue f r ρ A (MatrixRowQuotient.projectMatrix B X₀) :=
  selectedValue_eq_of_advice_eq f r ρ A _ _ (rowAdvice_projectMatrix i W A hW B X₀ T)

end
end PerfectCompleteness.TensorRowAdvice



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ChildBlockProjection
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.ChildBlockProjection

open RecursiveSpaces TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}

theorem fullJoint_pullback (rows : Nat → Nat)
    (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (arrays : Arrays projected rows) (x : Domain slots) :
    fullJoint (arraysPullback rows p arrays) x = fullJoint arrays (sourceProjection p x) := rfl

end
end PerfectCompleteness.ChildBlockProjection

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputReference

open scoped BigOperators TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

variable (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)

theorem query_readInput_hidden {Ω : Type*} (eval : Ω → UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : Exterior slots rows upper lower) :
    query slots rows upper lower W a
      (readInput slots rows upper lower W a eval
        ((HiddenBucketBias.splitTape W Ω tape).2, external))
      (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      sampledQuery slots rows upper lower a eval tape external := by
  funext x
  apply Prod.ext
  · exact (TensorBucketEvaluation.evaluate_apply_split W (UpperSpace slots upper)
      eval tape (restrictNode slots upper x)).symm
  · rfl

theorem response_readInput_hidden {Ω : Type*}
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (eval : Ω → UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : Exterior slots rows upper lower) :
    response slots rows upper lower W a labeling
      (readInput slots rows upper lower W a eval
        ((HiddenBucketBias.splitTape W Ω tape).2, external))
      (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (TreeCanonical.numberedFunction slots
          (sampledQuery slots rows upper lower a eval tape external))).1 := by
  unfold response
  rw [query_readInput_hidden]

end
end PerfectCompleteness.OwnInputReference



namespace PerfectCompleteness.OwnInputCanonicalQuery

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

theorem reorder_injective (hne : upper ≠ lower) (a : Block rows lower) :
    Function.Injective (reorder rows upper lower hne a) := by
  intro x y h
  apply Prod.ext
  · exact congrArg (fun z => z.2.1) h
  · apply Prod.ext
    · funext node
      rcases node with ⟨node, hn⟩
      by_cases hu : node = upper
      · subst node
        exact congrArg Prod.fst h
      · exact congrFun (congrArg (fun z => z.2.2) h) ⟨node, hu, hn⟩
    · exact Subsingleton.elim _ _

theorem sampledQuery_eq_reorder (hne : upper ≠ lower) (a : Block rows lower)
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    OwnInputReference.sampledQuery slots rows upper lower a eval tape external =
      reorder rows upper lower hne a ∘ BlockQuotient.projectBlock lower a ∘
        fullJoint (assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) := by
  funext x
  apply Prod.ext
  · change (fun row => (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape row).val
        (restrictNode slots upper x)) =
      fun row => ((assemble slots rows upper lower
        (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) upper row).val
          (restrictNode slots upper x)
    rw [assemble_upper]
  · apply Prod.ext
    · change DirectionQuotient.proj a
          (fun row => (external.lowerRows row).val (restrictNode slots lower x)) =
        DirectionQuotient.proj a
          (fun row => ((assemble slots rows upper lower
            (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) lower row).val
              (restrictNode slots lower x))
      rw [assemble_lower slots rows upper lower hne]
    · funext node row
      change (external.otherArrays node row).val (restrictNode slots node.val x) =
        ((assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) node.val row).val
            (restrictNode slots node.val x)
      rw [assemble_other]

theorem numbered_sampledQuery_eq (hne : upper ≠ lower) (a : Block rows lower)
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    TreeCanonical.numberedFunction slots
      (OwnInputReference.sampledQuery slots rows upper lower a eval tape external) =
      reorder rows upper lower hne a ∘ canonicalQuery slots rows lower a
        (assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) := by
  rw [sampledQuery_eq_reorder slots rows upper lower hne a eval tape external]
  rfl

theorem sampled_response_eq (hne : upper ≠ lower) (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (TreeCanonical.numberedFunction slots
          (OwnInputReference.sampledQuery slots rows upper lower a eval tape external)) =
      reorder rows upper lower hne a
        (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
          (canonicalQuery slots rows lower a (assemble slots rows upper lower
            (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external))) := by
  rw [numbered_sampledQuery_eq slots rows upper lower hne a eval tape external]
  exact KeyStrategy.response_postcomp_injective labeling .right
    (TreeCanonical.numberedSlots slots) _ (reorder rows upper lower hne a)
    (reorder_injective rows upper lower hne a)

theorem response_readInput_hidden_eq (hne : upper ≠ lower)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper)) (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace slots upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior slots rows upper lower) :
    OwnInputReference.response slots rows upper lower W a labeling
        (OwnInputReference.readInput slots rows upper lower W a eval
          ((HiddenBucketBias.splitTape W Ω tape).2, external))
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (canonicalQuery slots rows lower a (assemble slots rows upper lower
          (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external))).2.1
            ⟨upper, hne⟩ := by
  rw [OwnInputReference.response_readInput_hidden]
  exact congrArg Prod.fst (sampled_response_eq slots rows upper lower hne a labeling eval tape external)

end
end PerfectCompleteness.OwnInputCanonicalQuery

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputAffineSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OwnInputRawAssembly

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open OwnInputReference (RawSample ScalarSample UpperSpace UpperVector Cut)

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)

theorem backgroundOf_assemble
    (upperRows : Fin (rows (Nodes.height upper)) → H (nodeSlots slots upper))
    (external : OwnInputReference.Exterior slots rows upper lower) :
    HierarchicalMatrixTable.backgroundOf slots upper
        (OwnInputCanonicalQuery.assemble slots rows upper lower upperRows external) =
      HierarchicalMatrixTable.backgroundOf slots upper
        (OwnInputCanonicalQuery.assemble slots rows upper lower 0 external) := by
  funext node
  simp only [HierarchicalMatrixTable.backgroundOf, OwnInputCanonicalQuery.assemble,
    dite_eq_right node.property]

variable (W : Submodule F2 (UpperVector rows upper))
  (repeats : Nat → Nat) (cut : Cut upper lower)

theorem split_mergedTape (sample : RawSample slots rows upper lower W repeats cut) :
    HiddenBucketBias.splitTape W (ScalarSample slots upper lower repeats cut)
      (mergedTape slots rows upper lower W repeats cut sample) = (sample.1, sample.2.1) :=
  (HiddenBucketBias.splitTape W (ScalarSample slots upper lower repeats cut)).apply_symm_apply _

theorem arrays_upper (sample : RawSample slots rows upper lower W repeats cut) :
    arrays slots rows upper lower W repeats cut sample upper =
      BucketSampler.evaluate (rows (Nodes.height upper)) (scalarEval slots upper lower repeats cut)
        (mergedTape slots rows upper lower W repeats cut sample) :=
  OwnInputCanonicalQuery.assemble_upper slots rows upper lower _ _

theorem background_arrays (sample : RawSample slots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.backgroundOf slots upper
      (arrays slots rows upper lower W repeats cut sample) =
      background slots rows upper lower W repeats cut sample.2 :=
  backgroundOf_assemble slots rows upper lower _ sample.2.2

end
end PerfectCompleteness.OwnInputRawAssembly

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedSliceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalProjectedSlice

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projectedSlots upper)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedSlice.rowSpaceFintype
local instance valueFintype_ra40d01_1 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
theorem selectedValue_eq_some
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor projectedSlots upper A) :
    HierarchicalPrediction.selectedValue
        (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ) r ρ A
        (quotientMatrix originalSlots projectedSlots projection upper lowerLevel background A known T) =
      some (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value := by
  change HierarchicalPrediction.selectedValue _ r ρ A
    (MatrixRowQuotient.projectMatrix _ (TensorProjectedSlice.totalMatrix _ _ _ T)) = _
  rw [TensorRowAdvice.selectedValue_projectMatrix_eq (ProjectedNodeEmbedding.intoOriginal projection upper)
    (LinearMap.ker A) A le_rfl
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ) ρ
    (visibleMatrix originalSlots projectedSlots projection upper A known) T]
  simp only [HierarchicalPrediction.selectedValue, dite_eq_left hgood, witness,
    TensorSelectedSlice.witness]

theorem affinePrediction_eq_tensor
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor projectedSlots upper A) :
    HierarchicalPrediction.affinePrediction originalSlots upper lowerLevel background
        (matrix originalSlots projectedSlots projection upper A known T)
        (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value =
      visibleOffset originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood +
        TensorBucketEvaluation.tensorOutput (LinearMap.ker A)
          (nativeCorrection originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) T :=
  TensorProjectedSlice.prediction_eq_visible_add_tensorOutput (ProjectedNodeEmbedding.intoOriginal projection upper)
    (LinearMap.ker A) (visibleMatrix originalSlots projectedSlots projection upper A known) T
    (correction originalSlots upper lowerLevel background
      (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value)
    (witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value.1

end
end PerfectCompleteness.HierarchicalProjectedSlice


namespace PerfectCompleteness.ProjectedRawAssembly

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s k, MixedSupport.Projection (originalSlots s k) (projectedSlots s k))
  (rows : Nat → Nat) (upper lower : Nodes branch n)

variable (W : Submodule F2 (Block rows upper))
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

theorem visibleMatrix_apply
    (visible : OwnInputAffineSlice.VisibleSample projectedSlots rows upper lower W repeats cut)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace originalSlots upper)) :
    visibleMatrix originalSlots projectedSlots projection rows upper lower W repeats cut visible q =
      ∑ v : HiddenBucketBias.VisibleDirection W,
        (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.knownVisible projectedSlots rows upper lower W repeats cut visible v) •
            v.val.val :=
  HierarchicalTensorMatrix.visibleMatrix_apply originalSlots upper W
    (fun v => ProjectedNodeEmbedding.nativePullback projection upper
      (OwnInputRawAssembly.knownVisible projectedSlots rows upper lower W repeats cut visible v)) q

theorem background_arrays
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    HierarchicalMatrixTable.backgroundOf originalSlots upper
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) =
      background originalSlots projectedSlots projection rows upper lower W repeats cut sample.2 := by
  funext node row
  exact congrArg
    (fun bg : HierarchicalMatrixTable.Background (rows := rows) projectedSlots upper =>
      ProjectedNodeEmbedding.nativePullback projection node.val (bg node row))
    (OwnInputRawAssembly.background_arrays projectedSlots rows upper lower W repeats cut sample)

theorem matrix_arrays
    (sample : OwnInputReference.RawSample projectedSlots rows upper lower W repeats cut) :
    NodeEmbedding.matrix
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) upper =
      TensorProjectedSlice.totalMatrix (ProjectedNodeEmbedding.intoOriginal projection upper) W
        (visibleMatrix originalSlots projectedSlots projection rows upper lower W repeats cut sample.2)
        (OwnInputAffineSlice.hiddenOutput projectedSlots rows upper lower W repeats cut sample) := by
  apply LinearMap.ext
  intro q
  have hsplit := TensorBucketEvaluation.evaluate_splitTape W
    (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
    (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
    (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower W repeats cut sample)
  rw [OwnInputRawAssembly.split_mergedTape] at hsplit
  calc
    NodeEmbedding.matrix
        (arrays originalSlots projectedSlots projection rows upper lower W repeats cut sample) upper q =
        (fun row => (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.arrays projectedSlots rows upper lower W repeats cut sample upper row)) := rfl
    _ = (fun row => (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
        (BucketSampler.evaluate (rows (Nodes.height upper))
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
          (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower W repeats cut sample) row)) := by
      rw [OwnInputRawAssembly.arrays_upper]
    _ = TensorBucketEvaluation.visibleOutput W
          (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2.1 +
        TensorBucketEvaluation.tensorOutput W
          (q.comp (ProjectedNodeEmbedding.intoOriginal projection upper))
          (OwnInputAffineSlice.hiddenOutput projectedSlots rows upper lower W repeats cut sample) := hsplit
    _ = _ := by
      rw [TensorProjectedSlice.totalMatrix_apply,
        TensorProjectedSlice.includedEvaluation_eq_tensorOutput, visibleMatrix_apply]
      rfl

end
end PerfectCompleteness.ProjectedRawAssembly


namespace PerfectCompleteness.SourceProjectedCanonicalQuery

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  {slots projected : Slots branch n → Fin t → MixedSupport.Slot}
  (rows : Nat → Nat)
  (p : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))

theorem query_pullback {Y : Type*} (arrays : Arrays projected rows)
    (post : Output branch n rows → Y) :
    query rows (ChildBlockProjection.arraysPullback rows p arrays) post =
      query rows arrays post ∘ MixedSupport.projectionMap (TreeCanonical.numberedProjection p) := by
  funext x
  change post (fullJoint (ChildBlockProjection.arraysPullback rows p arrays)
      ((TreeCanonical.assignmentEquiv slots).symm x)) =
    post (fullJoint arrays ((TreeCanonical.assignmentEquiv projected).symm
      (MixedSupport.projectionMap (TreeCanonical.numberedProjection p) x)))
  rw [ChildBlockProjection.fullJoint_pullback, TreeCanonical.assignmentEquiv_symm_projection]

theorem response_pullback {Y : Type*} (arrays : Arrays projected rows)
    (post : Output branch n rows → Y)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
        (query rows (ChildBlockProjection.arraysPullback rows p arrays) post) =
      KeyStrategy.response labeling side (TreeCanonical.numberedSlots projected)
        (query rows arrays post) := by
  rw [query_pullback]
  exact KeyStrategy.response_projection labeling side (TreeCanonical.numberedProjection p)
    (query rows arrays post)

theorem canonical_response_pullback (lower : Nodes branch n) (a : Block rows lower)
    (arrays : Arrays projected rows)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (side : CanonicalKeys.Side) :
    KeyStrategy.response labeling side (TreeCanonical.numberedSlots slots)
        (OwnInputCanonicalQuery.canonicalQuery slots rows lower a
          (ChildBlockProjection.arraysPullback rows p arrays)) =
      KeyStrategy.response labeling side (TreeCanonical.numberedSlots projected)
        (OwnInputCanonicalQuery.canonicalQuery projected rows lower a arrays) :=
  response_pullback rows p arrays (BlockQuotient.projectBlock lower a) labeling side

theorem response_readInput_hidden (upper lower : Nodes branch n) (hne : upper ≠ lower)
    (W : Submodule F2 (OwnInputReference.UpperVector rows upper)) (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    {Ω : Type*} (eval : Ω → OwnInputReference.UpperSpace projected upper)
    (tape : BucketSampler.Tape (rows (Nodes.height upper)) Ω)
    (external : OwnInputReference.Exterior projected rows upper lower) :
    OwnInputReference.response projected rows upper lower W a labeling
        (OwnInputReference.readInput projected rows upper lower W a eval
          ((HiddenBucketBias.splitTape W Ω tape).2, external))
        (HiddenBucketBias.hiddenSum W eval (HiddenBucketBias.splitTape W Ω tape).1) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots slots)
        (OwnInputCanonicalQuery.canonicalQuery slots rows lower a
          (ChildBlockProjection.arraysPullback rows p
            (OwnInputCanonicalQuery.assemble projected rows upper lower
              (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external)))).2.1
                ⟨upper, hne⟩ := by
  have h := OwnInputCanonicalQuery.response_readInput_hidden_eq projected rows upper lower
    hne W a labeling eval tape external
  rw [← canonical_response_pullback rows p lower a
    (OwnInputCanonicalQuery.assemble projected rows upper lower
      (BucketSampler.evaluate (rows (Nodes.height upper)) eval tape) external) labeling .right] at h
  exact h

end
end PerfectCompleteness.SourceProjectedCanonicalQuery


namespace PerfectCompleteness.HierarchicalProjectedRawPrediction

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch : Nat → Nat} {n t : Nat}
  (originalSlots projectedSlots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (originalSlots s j) (projectedSlots s j))
  (rows : Nat → Nat) (upper lower : Nodes branch n) (lowerLevel : Nat)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays originalSlots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rowSpaceFintype
local instance valueFintype_ra40d01_2 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
theorem response_eq_canonical (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : Raw projectedSlots rows upper lower A repeats cut) :
    OwnInputReference.response projectedSlots rows upper lower (LinearMap.ker A) a labeling
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2)
        (hidden projectedSlots rows upper lower A repeats cut sample) =
      (KeyStrategy.response labeling .right (TreeCanonical.numberedSlots originalSlots)
        (OwnInputCanonicalQuery.canonicalQuery originalSlots rows lower a
          (rawArrays originalSlots projectedSlots projection rows upper lower A repeats cut sample))).2.1
            ⟨upper, cut.upper_ne_lower⟩ := by
  have h := SourceProjectedCanonicalQuery.response_readInput_hidden rows projection upper lower
    cut.upper_ne_lower (LinearMap.ker A) a labeling
    (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut)
    (OwnInputRawAssembly.mergedTape projectedSlots rows upper lower (LinearMap.ker A) repeats cut sample)
    sample.2.2
  rw [OwnInputRawAssembly.split_mergedTape] at h
  exact h

theorem response_eq_rightUpper (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : Raw projectedSlots rows upper lower A repeats cut) :
    OwnInputReference.response projectedSlots rows upper lower (LinearMap.ker A) a labeling
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2)
        (hidden projectedSlots rows upper lower A repeats cut sample) =
      HierarchicalPrediction.rightUpper originalSlots upper
        (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample.2)
        labeling lower cut.upper_ne_lower a
        (rawMatrix originalSlots projectedSlots projection rows upper lower A repeats cut sample) := by
  dsimp only [visibleBackground, rawMatrix, rawArrays]
  rw [← ProjectedRawAssembly.background_arrays originalSlots projectedSlots projection rows upper lower
    (LinearMap.ker A) repeats cut sample,
    HierarchicalPrediction.rightUpper, HierarchicalMatrixTable.displayed_original]
  exact response_eq_canonical originalSlots projectedSlots projection rows upper lower A repeats cut
    a labeling sample

theorem response_eq_rightUpper_totalMatrix (a : Block rows lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (sample : Raw projectedSlots rows upper lower A repeats cut) :
    OwnInputReference.response projectedSlots rows upper lower (LinearMap.ker A) a labeling
        (OwnInputReference.readInput projectedSlots rows upper lower (LinearMap.ker A) a
          (OwnInputRawAssembly.scalarEval projectedSlots upper lower repeats cut) sample.2)
        (hidden projectedSlots rows upper lower A repeats cut sample) =
      HierarchicalPrediction.rightUpper originalSlots upper
        (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample.2)
        labeling lower cut.upper_ne_lower a
        (HierarchicalProjectedSlice.matrix originalSlots projectedSlots projection upper A
          (known projectedSlots rows upper lower A repeats cut sample.2)
          (hidden projectedSlots rows upper lower A repeats cut sample)) := by
  exact (response_eq_rightUpper originalSlots projectedSlots projection rows upper lower A repeats cut
    a labeling sample).trans (congrArg
      (fun X : HierarchicalMatrixTable.Matrix (rows := rows) originalSlots upper =>
        HierarchicalPrediction.rightUpper originalSlots upper
          (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample.2)
          labeling lower cut.upper_ne_lower a X)
      (ProjectedRawAssembly.matrix_arrays originalSlots projectedSlots projection rows upper lower
        (LinearMap.ker A) repeats cut sample))

theorem rawJ_eq_tensorJ (sample : Raw projectedSlots rows upper lower A repeats cut) :
    rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut sample =
      tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut
        sample.2 (hidden projectedSlots rows upper lower A repeats cut sample) := by
  exact congrArg₂
    (fun (b : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)
        (X : HierarchicalMatrixTable.Matrix (rows := rows) originalSlots upper) =>
      GoodAdviceEvents.J
        (HierarchicalUsefulness.table originalSlots upper lowerLevel original originalArrays lowerEvent κ σ b)
        r ρ (A, HierarchicalPrediction.quotientMatrix originalSlots upper lowerLevel b X))
    (ProjectedRawAssembly.background_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut sample)
    (ProjectedRawAssembly.matrix_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A) repeats cut sample)

theorem rawPrediction_eq_oai (a : Block rows lower) (v : Visible projectedSlots rows upper lower A repeats cut)
    (hgood : VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v) (sample : Raw projectedSlots rows upper lower A repeats cut) (hv : sample.2 = v) :
    rawPrediction originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a sample =
      (rawJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut sample &&
      responseMatch originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut a v hgood sample) := by
  have hbg := ProjectedRawAssembly.background_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A)
    repeats cut sample
  have hmat := ProjectedRawAssembly.matrix_arrays originalSlots projectedSlots projection rows upper lower (LinearMap.ker A)
    repeats cut sample
  have hresponse := response_eq_rightUpper_totalMatrix originalSlots projectedSlots projection rows upper lower A repeats cut a σ sample
  rw [hv] at hbg hmat hresponse
  change rawBackground originalSlots projectedSlots projection rows upper lower A repeats cut sample =
    visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v at hbg
  change rawMatrix originalSlots projectedSlots projection rows upper lower A repeats cut sample =
    HierarchicalProjectedSlice.matrix originalSlots projectedSlots projection upper A
      (known projectedSlots rows upper lower A repeats cut v)
      (hidden projectedSlots rows upper lower A repeats cut sample) at hmat
  have hprediction := congrArg₂
    (fun (b : HierarchicalMatrixTable.Background (rows := rows) originalSlots upper)
        (X : HierarchicalMatrixTable.Matrix (rows := rows) originalSlots upper) =>
      HierarchicalPrediction.prediction originalSlots upper lowerLevel b σ lower cut.upper_ne_lower a
        original originalArrays lowerEvent κ r ρ A X) hbg hmat
  unfold rawPrediction
  rw [hprediction, rawJ_eq_tensorJ]
  simp only [hv]
  dsimp only [HierarchicalPrediction.prediction]
  rw [HierarchicalProjectedSlice.selectedValue_eq_some originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)
    hgood (hidden projectedSlots rows upper lower A repeats cut sample)]
  dsimp only
  rw [HierarchicalProjectedSlice.affinePrediction_eq_tensor originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)
    hgood (hidden projectedSlots rows upper lower A repeats cut sample), ← hresponse]
  simp only [tensorJ, HierarchicalProjectedSlice.J, responseMatch, hv,
    TensorBucketEvaluation.tensorOutput]
  all_goals
    apply congrArg₂ (fun first second : Bool => first && second)
    · rfl
    · exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rawPrediction_eq_oai.{u_1} := @OAI.PerfectCompleteness.HierarchicalProjectedRawPrediction.rawPrediction_eq_oai.{u_1}
