-- Prove2me | solution 1 for OAI.PerfectCompleteness.RepresentativeBucketCollision.collision_probability_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:15:50.607201+00:00
-- url     : https://prove2.me/submissions/76753830-ea3d-4332-8e97-c140136df2e9

import Lean.Elab.Tactic.Omega
import Mathlib
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Equiv.Defs
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
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Piecewise
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Factorial.Basic
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
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Abel
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Std
import Definitions.Def_OAIQ252P015

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearGramCompressionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixRowQuotient

noncomputable section

variable {𝕜 H K : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup K] [Module 𝕜 K]

theorem residual_factorization (W : Submodule 𝕜 H)
    (s : (H ⧸ W) →ₗ[𝕜] H) (hs : W.mkQ.comp s = LinearMap.id)
    (X : Module.Dual 𝕜 H →ₗ[𝕜] K) :
    X - liftMatrix W s (projectMatrix W X) =
      (X.comp (residualVector W s hs).dualMap).comp W.subtype.dualMap := by
  apply LinearMap.ext
  intro q
  change X q - X (W.mkQ.dualMap (s.dualMap q)) =
    X ((residualVector W s hs).dualMap (W.subtype.dualMap q))
  rw [← map_sub]
  apply congrArg X
  apply LinearMap.ext
  intro h
  change q h - q (s (W.mkQ h)) = q (h - s (W.mkQ h))
  rw [map_sub]

end
end PerfectCompleteness.MatrixRowQuotient

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_LinearEvaluationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DirectionQuotient

variable {V B : Type*} [AddCommGroup V] [Module F2 V]

theorem mem_line_iff (a x : V) : x ∈ line a ↔ x = 0 ∨ x = a := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx
    rcases UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases c with hzero | hone
    · left
      simpa only [hzero, zero_smul] using hc.symm
    · right
      simpa only [hone, one_smul] using hc.symm
  · rintro (rfl | rfl)
    · exact (line a).zero_mem
    · exact Submodule.mem_span_singleton_self _

theorem proj_eq_zero_iff (a x : V) : proj a x = 0 ↔ x = 0 ∨ x = a :=
  (Submodule.Quotient.mk_eq_zero (line a)).trans (mem_line_iff a x)

open MixedSupport CanonicalKeys

end PerfectCompleteness.DirectionQuotient

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuotientTableAgreementLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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

end
end PerfectCompleteness.KeyStrategy

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_CanonicalMatrixTable
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.HPullback_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.sourceProjection_apply _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.CanonicalMatrixTable

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)

theorem rightQuery_shift (a : K) (X : Matrix (K := K) slots H) (h : H) :
    rightQuery slots H other a (EvaluationMatrix.shift H X a h) =
      rightQuery slots H other a X := by
  funext x
  apply Prod.ext
  · change DirectionQuotient.proj a
        (EvaluationMatrix.evaluate H X x + h.val x • a) =
      DirectionQuotient.proj a (EvaluationMatrix.evaluate H X x)
    rw [map_add, map_smul]
    have ha : DirectionQuotient.proj a a = 0 :=
      (DirectionQuotient.proj_eq_zero_iff a a).mpr (Or.inr rfl)
    simp [ha]
  · rfl

theorem rightResponse_shift (a : K) (X : Matrix (K := K) slots H) (h : H) :
    KeyStrategy.response σ .right slots
        (rightQuery slots H other a (EvaluationMatrix.shift H X a h)) =
      KeyStrategy.response σ .right slots (rightQuery slots H other a X) := by
  rw [rightQuery_shift]

theorem accepts_iff (a : K) (X : Matrix (K := K) slots H) :
    Accepts slots H other σ a X ↔
      DirectionQuotient.projectWithSide a (response slots H other σ X) =
        KeyStrategy.response σ .right slots (rightQuery slots H other a X) :=
  CanonicalEdges.coarsen_eq_iff slots (query slots H other X)
    (DirectionQuotient.projectWithSide a) _ _

theorem accepted_response_in_fiber (a : K) (X : Matrix (K := K) slots H) (h : H)
    (hacc : Accepts slots H other σ a (EvaluationMatrix.shift H X a h)) :
    DirectionQuotient.projectWithSide a
        (response slots H other σ (EvaluationMatrix.shift H X a h)) =
      KeyStrategy.response σ .right slots (rightQuery slots H other a X) := by
  have h := (accepts_iff slots H other σ a (EvaluationMatrix.shift H X a h)).mp hacc
  rwa [rightResponse_shift] at h

end
end PerfectCompleteness.CanonicalMatrixTable

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixTriangularFoldingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.MatrixTriangularFolding

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)

theorem query_add (X Δ : CanonicalMatrixTable.Matrix (K := K) slots H) (d : Z → K)
    (hΔ : ∀ x, EvaluationMatrix.evaluate H Δ x = d (other x)) :
    CanonicalMatrixTable.query slots H other (X + Δ) =
      TriangularFolding.translate d ∘ CanonicalMatrixTable.query slots H other X := by
  funext x
  apply Prod.ext
  · change X (EvaluationMatrix.evaluation H x) + Δ (EvaluationMatrix.evaluation H x) =
      X (EvaluationMatrix.evaluation H x) + d (other x)
    rw [← hΔ x]
    rfl
  · rfl

theorem response_add (X Δ : CanonicalMatrixTable.Matrix (K := K) slots H) (d : Z → K)
    (hΔ : ∀ x, EvaluationMatrix.evaluate H Δ x = d (other x)) :
    CanonicalMatrixTable.response slots H other σ (X + Δ) =
      TriangularFolding.translate d (CanonicalMatrixTable.response slots H other σ X) := by
  unfold CanonicalMatrixTable.response
  rw [query_add slots H other X Δ d hΔ]
  exact KeyStrategy.response_postcomp_injective σ .left slots
    (CanonicalMatrixTable.query slots H other X) (TriangularFolding.translate d)
    (TriangularFolding.translate d).injective

end
end PerfectCompleteness.MatrixTriangularFolding



namespace PerfectCompleteness.RepresentativeMatrixTable

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)

theorem sideEvaluation_at_image (hW : Determined slots H other W)
    (x : Assignment slots) :
    sideEvaluation slots H other W (other x) =
      (EvaluationMatrix.evaluation H x).comp W.subtype := by
  have hx : other x ∈ Set.range other := ⟨x, rfl⟩
  rw [sideEvaluation, dite_eq_left hx]
  ext b
  exact hW b _ x (Classical.choose_spec hx)

theorem raw_response (hW : Determined slots H other W)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    CanonicalMatrixTable.response slots H other σ X =
      TriangularFolding.translate (fun z => X (correctionFunctional slots H other W s hs z))
        (response slots H other σ W s X) := by
  let Δ := (X.comp (MatrixRowQuotient.residualVector W s hs).dualMap).comp W.subtype.dualMap
  have hΔ : ∀ x, EvaluationMatrix.evaluate H Δ x =
      X (correctionFunctional slots H other W s hs (other x)) := by
    intro x
    unfold correctionFunctional
    rw [sideEvaluation_at_image slots H other W hW x]
    rfl
  have hsum : representative slots H W s X + Δ = X := by
    have he := MatrixRowQuotient.residual_factorization W s hs X
    change X - representative slots H W s X = Δ at he
    rw [← he]
    abel
  have hr := MatrixTriangularFolding.response_add slots H other σ
    (representative slots H W s X) Δ
    (fun z => X (correctionFunctional slots H other W s hs z)) hΔ
  rw [hsum] at hr
  exact hr

theorem response_eq_normalize (hW : Determined slots H other W)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    response slots H other σ W s X =
      normalizeOutput slots H other W s hs X (CanonicalMatrixTable.response slots H other σ X) := by
  rw [raw_response slots H other σ W s hs hW X]
  apply Prod.ext
  · change (response slots H other σ W s X).1 =
      (response slots H other σ W s X).1 +
        X (correctionFunctional slots H other W s hs (response slots H other σ W s X).2) -
        X (correctionFunctional slots H other W s hs (response slots H other σ W s X).2)
    abel
  · rfl

theorem project_normalize_shift (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H)
    (h : H) (y : K × Z) :
    DirectionQuotient.projectWithSide a
      (normalizeOutput slots H other W s hs (EvaluationMatrix.shift H X a h) y) =
      normalizeQuotient slots H other W s hs a X (DirectionQuotient.projectWithSide a y) := by
  apply Prod.ext
  · change DirectionQuotient.proj a
        (y.1 - (X (correctionFunctional slots H other W s hs y.2) +
          correctionFunctional slots H other W s hs y.2 h • a)) =
      DirectionQuotient.proj a y.1 - DirectionQuotient.proj a
        (X (correctionFunctional slots H other W s hs y.2))
    have ha : DirectionQuotient.proj a a = 0 :=
      (DirectionQuotient.proj_eq_zero_iff a a).mpr (Or.inr rfl)
    simp only [map_sub, map_add, map_smul, ha, smul_zero, add_zero]
  · rfl

theorem accepted_response_in_fiber (hW : Determined slots H other W)
    (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H) (h : H)
    (hacc : CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h)) :
    DirectionQuotient.projectWithSide a
      (response slots H other σ W s (EvaluationMatrix.shift H X a h)) =
      normalizeQuotient slots H other W s hs a X
        (KeyStrategy.response σ .right slots (CanonicalMatrixTable.rightQuery slots H other a X)) := by
  rw [response_eq_normalize slots H other σ W s hs hW]
  rw [project_normalize_shift]
  rw [CanonicalMatrixTable.accepted_response_in_fiber slots H other σ a X h hacc]

include hs in
theorem card_accepted_responses_le_two [Finite K] [Finite Z]
    (hW : Determined slots H other W) (a : K) (ha : a ≠ 0)
    (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    Nat.card {y : K × Z // ∃ h : H,
      CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
      response slots H other σ W s (EvaluationMatrix.shift H X a h) = y} ≤ 2 := by
  let z := normalizeQuotient slots H other W s hs a X
    (KeyStrategy.response σ .right slots (CanonicalMatrixTable.rightQuery slots H other a X))
  let intoFiber :
      {y : K × Z // ∃ h : H,
        CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
        response slots H other σ W s (EvaluationMatrix.shift H X a h) = y} →
      {y : K × Z // DirectionQuotient.projectWithSide a y = z} := fun y =>
    ⟨y.val, by
      obtain ⟨h, hacc, hy⟩ := y.property
      rw [← hy]
      exact accepted_response_in_fiber slots H other σ W s hs hW a X h hacc⟩
  calc
    _ ≤ Nat.card {y : K × Z // DirectionQuotient.projectWithSide a y = z} :=
      Nat.card_le_card_of_injective intoFiber (by
        intro y y' he
        exact Subtype.ext (congrArg
          (fun v : {y : K × Z // DirectionQuotient.projectWithSide a y = z} => v.val) he))
    _ = 2 := DirectionQuotient.card_projectWithSide_fiber a ha z

end
end PerfectCompleteness.RepresentativeMatrixTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_TwoResponseCollisionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.DecoderTableCoupling.definedEqual_collision _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TwoResponseCollision

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω Y : Type*} [Fintype Ω] [Fintype Y]

theorem goodDefined_weight_eq_sum (μ : FiniteDistribution Ω) (f : Ω → Option Y)
    (good : Ω → Bool) (x : Ω) :
    (if goodDefined f good x then μ.weight x else 0) =
      ∑ y, if responds f good y x then μ.weight x else 0 := by
  cases hg : good x <;> cases hf : f x <;>
    simp [goodDefined, responds, hg, hf, eq_comm]

theorem goodDefined_probability_eq_sum (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool) :
    μ.probability (goodDefined f good) = ∑ y, responseMass μ f good y := by
  change (∑ x, if goodDefined f good x then μ.weight x else 0) =
    ∑ y, ∑ x, if responds f good y x then μ.weight x else 0
  simp_rw [goodDefined_weight_eq_sum]
  exact Finset.sum_comm

theorem goodCollision_weight_eq_sum (μ : FiniteDistribution Ω) (f : Ω → Option Y)
    (good : Ω → Bool) (x x' : Ω) :
    (if goodCollision f good (x, x') then μ.weight x * μ.weight x' else 0) =
      ∑ y, (if responds f good y x then μ.weight x else 0) *
        (if responds f good y x' then μ.weight x' else 0) := by
  cases hg : good x <;> cases hg' : good x' <;>
    cases hf : f x <;> cases hf' : f x' <;>
    simp [goodCollision, collision, responds, hg, hg', hf, hf', ite_mul, mul_ite, eq_comm]

theorem goodCollision_probability_eq_sum_sq (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool) :
    (μ.product μ).probability (goodCollision f good) =
      ∑ y, responseMass μ f good y ^ 2 := by
  change (∑ p : Ω × Ω,
    if goodCollision f good p then μ.weight p.1 * μ.weight p.2 else 0) = _
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ x, ∑ x', ∑ y,
        (if responds f good y x then μ.weight x else 0) *
          (if responds f good y x' then μ.weight x' else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro x' _
      exact goodCollision_weight_eq_sum μ f good x x'
    _ = ∑ x, ∑ y, ∑ x',
        (if responds f good y x then μ.weight x else 0) *
          (if responds f good y x' then μ.weight x' else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      exact Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ x',
        (if responds f good y x then μ.weight x else 0) *
          (if responds f good y x' then μ.weight x' else 0) := Finset.sum_comm
    _ = ∑ y, responseMass μ f good y ^ 2 := by
      apply Finset.sum_congr rfl
      intro y _
      change (∑ x, ∑ x',
        (if responds f good y x then μ.weight x else 0) *
          (if responds f good y x' then μ.weight x' else 0)) =
        (∑ x, if responds f good y x then μ.weight x else 0) ^ 2
      rw [← Finset.sum_mul_sum, pow_two]

omit [Fintype Y] in
theorem responseMass_eq_zero_of_not_goodResponse (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool) (y : Y)
    (hy : ¬GoodResponse f good y) : responseMass μ f good y = 0 := by
  unfold responseMass FiniteDistribution.probability
  apply Finset.sum_eq_zero
  intro x _
  by_cases hg : good x = true
  · have hf : f x ≠ some y := fun hf => hy ⟨x, hg, hf⟩
    simp [responds, hg, hf]
  · simp [responds, hg]

theorem sum_sq_bound_of_support_card_le_two (q : Y → ℝ) (R : Y → Prop)
    (hzero : ∀ y, ¬R y → q y = 0)
    (hcard : Nat.card {y : Y // R y} ≤ 2) :
    (∑ y, q y) ^ 2 ≤ 2 * ∑ y, q y ^ 2 := by
  let S : Finset Y := Finset.univ.filter R
  have hsum : (∑ y ∈ S, q y) = ∑ y, q y := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y _ hy
    exact hzero y (by simpa [S] using hy)
  have hsumSq : (∑ y ∈ S, q y ^ 2) = ∑ y, q y ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro y _ hy
    rw [hzero y (by simpa [S] using hy)]
    norm_num
  have hcardNat : S.card ≤ 2 := by
    simpa [Nat.card_eq_fintype_card, Fintype.card_subtype, S] using hcard
  have hcardReal : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcardNat
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : Y => (1 : ℝ)) q
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hsum, hsumSq] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right hcardReal
    (Finset.sum_nonneg (fun y _ => sq_nonneg (q y))))

theorem goodCollision_probability_ge (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool)
    (hcard : Nat.card {y : Y // GoodResponse f good y} ≤ 2) :
    μ.probability (goodDefined f good) ^ 2 / 2 ≤
      (μ.product μ).probability (goodCollision f good) := by
  rw [goodDefined_probability_eq_sum, goodCollision_probability_eq_sum_sq]
  have h := sum_sq_bound_of_support_card_le_two (responseMass μ f good)
    (GoodResponse f good) (responseMass_eq_zero_of_not_goodResponse μ f good) hcard
  linarith

theorem collision_probability_ge (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool)
    (hcard : Nat.card {y : Y // GoodResponse f good y} ≤ 2) :
    μ.probability (goodDefined f good) ^ 2 / 2 ≤
      (μ.product μ).probability (collision f) := by
  apply (goodCollision_probability_ge μ f good hcard).trans
  apply FiniteDistribution.probability_mono
  intro p hp
  exact (Bool.and_eq_true_iff.mp hp).2

theorem collision_probability_ge_of_response_set (μ : FiniteDistribution Ω)
    (f : Ω → Option Y) (good : Ω → Bool) (R : Y → Prop)
    (hcard : Nat.card {y : Y // R y} ≤ 2)
    (hR : ∀ x y, good x = true → f x = some y → R y) :
    μ.probability (goodDefined f good) ^ 2 / 2 ≤
      (μ.product μ).probability (collision f) := by
  let into : {y : Y // GoodResponse f good y} → {y : Y // R y} := fun y =>
    ⟨y.val, by
      obtain ⟨x, hg, hf⟩ := y.property
      exact hR x y.val hg hf⟩
  have hi : Function.Injective into := by
    intro y y' h
    exact Subtype.ext (congrArg (fun z : {y : Y // R y} => z.val) h)
  apply collision_probability_ge μ f good
  exact (Nat.card_le_card_of_injective into hi).trans hcard

end
end PerfectCompleteness.TwoResponseCollision



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RepresentativeBucketCollisionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalArrays.joint_component _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.TreeCanonical.assignmentEquiv_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.HPullback_apply _root_.OAI.PerfectCompleteness.TreeSourceSpaces.sourceProjection_apply _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RepresentativeBucketCollision

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport CanonicalKeys
open DirectionQuotient (F2)
open TwoResponseCollision
open UniqueGamesTheorem.Foundations.Games

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)

theorem bucketTable_eq_some_iff
    (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
    (a : K) (X : CanonicalMatrixTable.Matrix (K := K) slots H) (h : H) (y : K × Z) :
    bucketTable slots H other σ W s useful a X h = some y ↔
      useful (MatrixRowQuotient.projectMatrix W (EvaluationMatrix.shift H X a h)) ∧
        RepresentativeMatrixTable.response slots H other σ W s
          (EvaluationMatrix.shift H X a h) = y := by
  by_cases hu : useful (MatrixRowQuotient.projectMatrix W (EvaluationMatrix.shift H X a h)) <;>
    simp [bucketTable, RepresentativeMatrixTable.partialTable,
      RepresentativeMatrixTable.response, RepresentativeMatrixTable.representative, hu]

include hs in

theorem collision_probability_lower_bound_oai [Finite K] [Finite Z] [Fintype H]
    (hW : RepresentativeMatrixTable.Determined slots H other W)
    (μ : FiniteDistribution H)
    (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
    (a : K) (ha : a ≠ 0) (X : CanonicalMatrixTable.Matrix (K := K) slots H) :
    μ.probability (goodDefined (bucketTable slots H other σ W s useful a X)
        (bucketAccepted slots H other σ a X)) ^ 2 / 2 ≤
      (μ.product μ).probability
        (collision (bucketTable slots H other σ W s useful a X)) := by
  let : Fintype K := Fintype.ofFinite K
  let : Fintype Z := Fintype.ofFinite Z
  apply collision_probability_ge_of_response_set μ
    (bucketTable slots H other σ W s useful a X) (bucketAccepted slots H other σ a X)
    (fun y => ∃ h : H,
      CanonicalMatrixTable.Accepts slots H other σ a (EvaluationMatrix.shift H X a h) ∧
        RepresentativeMatrixTable.response slots H other σ W s
          (EvaluationMatrix.shift H X a h) = y)
  · exact RepresentativeMatrixTable.card_accepted_responses_le_two
      slots H other σ W s hs hW a ha X
  · intro h y hgood hresponse
    refine ⟨h, ?_, ?_⟩
    · simpa only [bucketAccepted, decide_eq_true_eq] using hgood
    · exact ((bucketTable_eq_some_iff slots H other σ W s useful a X h y).mp hresponse).2

end
end PerfectCompleteness.RepresentativeBucketCollision



end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PerfectCompleteness.RepresentativeBucketCollision.collision_probability_lower_bound_oai.{u_1, u_2} := @OAI.PerfectCompleteness.RepresentativeBucketCollision.collision_probability_lower_bound_oai.{u_1, u_2}
