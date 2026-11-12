-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedStoppedMeetingEquality.meeting_probability_eq_expectedMeeting
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:23:24.75522+00:00
-- url     : https://prove2.me/submissions/103b01a1-f801-4bb0-9a45-03682c640afe

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
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedMeetingEquality_native_expectation_eq_cleanMeeting
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedMeetingEquality_physical_expectation_eq_expectedMeeting
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedNativeProjection_projection_heq
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedNativeProjection_rightSlots_eq
import Theorems.Thm_OAI_PerfectCompleteness_FixedStoppedNativeTape_visible_heq

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Question-dependent stochastic responses are derandomized by sampling complete
answer tables independently before the questions. The table law, marginal law,
and mixture identity are proved from finite products and sums. No derandomization
principle is assumed as a hypothesis or axiom.
-/

namespace UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteDistribution
variable {Ω Γ Q A : Type*} [Fintype Ω] [Fintype Γ] [Fintype Q] [Fintype A]

theorem expectation_congr (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x = g x) : μ.expectation f = μ.expectation g := by
  unfold expectation
  apply Finset.sum_congr rfl
  intro x _
  rw [h x]
end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_SourceQuestionPositionSplit
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SourceQuestionPositionSplit

noncomputable section

open scoped Classical
open RecursiveSpaces SourceQuestionReconstruction TreeSourceSpaces
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n t m : Nat}

theorem tree_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t)) :
    SourceChildQuestionLaw.assembleEquiv designated (join designated q positions) =
      fun leaf k => (q leaf k, positions leaf k) :=
  (SourceChildQuestionLaw.assembleEquiv (m := m) (t := t) designated).apply_symm_apply _

theorem child_tree_join (designated : Fin (branch n) → Slots branch n)
    (q : Questions (branch := branch) (n := n) (t := t) (m := m))
    (positions : Positions (branch := branch) (n := n) (t := t))
    (i : Fin (branch n)) (leaf : Slots branch n) (k : Fin t) :
    SourceChildKernel.tree designated i (join designated q positions i) leaf k =
      (q (i, leaf) k, positions (i, leaf) k) :=
  congrFun (congrFun (tree_join designated q positions) (i, leaf)) k

end
end PerfectCompleteness.SourceQuestionPositionSplit

end

end OAI
end

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_CandidateCoupling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularTable.Top.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CandidateCoupling

open PreliminarySampler PreliminaryAveraging TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators Classical

noncomputable section

section Selection

variable {I : Type*} [Fintype I] [DecidableEq I]
  {D : I → Type*} [∀ i, Fintype (D i)]

omit [DecidableEq I] in
theorem expectation_sigmaLaw (μ : FiniteDistribution I)
    (ν : ∀ i, FiniteDistribution (D i)) (f : (Σ i, D i) → ℝ) :
    (CompletionSoundness.sigmaLaw μ ν).expectation f =
      μ.expectation (fun i => (ν i).expectation (fun d => f ⟨i, d⟩)) := by
  simp only [FiniteDistribution.expectation, CompletionSoundness.sigmaLaw,
    Fintype.sum_sigma, Finset.mul_sum, mul_assoc]

end Selection

end
end PerfectCompleteness.CandidateCoupling

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

end PathTransport

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

end
end PerfectCompleteness.FixedStoppedNativeProjection

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_ProjectedMeetingTransport
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedMeetingTransport

noncomputable section

open scoped Classical
open RecursiveSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype RightDecoder.scalarFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  {Sample : OriginalDecoderMark.SlotFamily branch plan.depth t → Type*}
  [∀ slots, Fintype (Sample slots)]
  (F : OriginalDecoderMark.Family branch (FixedRows.rows plan) plan.depth t Sample)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (slots projected : Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower) (cut : OwnInputReference.Cut upper lower)
  (threshold : ℝ)
  (visible : HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan)
    upper lower A (FixedRows.repeats plan) cut)

local instance physicalLeftFintype_r99acde_1 {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual (ZMod 2) (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
theorem familyMeetingProbability_congr
    (target other : Slots branch plan.depth → Fin t → MixedSupport.Slot)
    (otherLower : Nodes branch plan.depth)
    (projection' : ∀ s j, MixedSupport.Projection (target s j) (other s j))
    (a' : Block (FixedRows.rows plan) otherLower)
    (cut' : OwnInputReference.Cut upper otherLower)
    (visible' : HierarchicalProjectedRawPrediction.Visible other (FixedRows.rows plan)
      upper otherLower A (FixedRows.repeats plan) cut')
    (hs : slots = target) (hp : projected = other) (hl : lower = otherLower)
    (hprojection : HEq projection projection') (ha : HEq a a')
    (hcut : HEq cut cut') (hvisible : HEq visible visible') :
    familyMeetingProbability plan F σ slots projected projection upper lower lowerLevel
        A a cut threshold visible =
      familyMeetingProbability plan F σ target other projection' upper otherLower lowerLevel
        A a' cut' threshold visible' := by
  cases hs
  cases hp
  cases hl
  have hprojection' : projection = projection' := eq_of_heq hprojection
  cases hprojection'
  have ha' : a = a' := eq_of_heq ha
  cases ha'
  have hcut' : cut = cut' := eq_of_heq hcut
  cases hcut'
  have hvisible' : visible = visible' := eq_of_heq hvisible
  cases hvisible'
  rfl

end
end PerfectCompleteness.ProjectedMeetingTransport

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_SlotProjectedExperiment
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SlotProjectedExperiment

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

variable {branch : Nat → Nat} {n i j t v m : Nat}

variable (rows repeats : Nat → Nat) (hupper : j + 1 ≤ n) (hij : i < j)
  (pref : GeometricCutSplit.Prefix branch n (j + 1))

variable (slots : Slots branch n → Fin t → MixedSupport.Slot)

variable (hbranch : ∀ k < j + 1, 0 < branch k) (hrows : ∀ k, 0 < rows (k + 1))
  (flag : Fin (branch i) → FiniteDistribution Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

section Source

variable (clauses : Fin m → SourceClause.NormalizedClause v)
  (designated : Fin (branch i) → Slots branch i)
  (q : SourceQuestionPositionSplit.Questions (branch := branch) (n := i) (t := t) (m := m))
  (choices : SourceQuestionKernelJoint.ChoiceTuple (branch := branch) (n := i) (t := t))
  (flags : SourceProjectedTag.Flags (branch := branch) (n := i))

private theorem tree_sources (leaf : Slots branch (i + 1)) (a : Fin t) :
    SourceChildKernel.tree designated leaf.1
      (SourceQuestionKernelJoint.sources designated q choices leaf.1) leaf.2 a =
      (q leaf a, choices leaf.1 leaf.2 a) := by
  rcases leaf with ⟨child, tail⟩
  have h := SourceQuestionPositionSplit.child_tree_join designated q
    (SourceQuestionPositionSplit.byChild.symm choices) child tail a
  change SourceChildKernel.tree designated child
    (SourceQuestionKernelJoint.sources designated q choices child) tail a =
      (q (child, tail) a, choices child tail a) at h
  exact h

theorem mixedInside_source :
    mixedInside (SourceProjectedTag.originalSlots clauses q) choices flags =
      SourceProjectedTag.mixedInside clauses designated q choices flags := by
  funext leaf a
  have htree := tree_sources designated q choices leaf a
  cases hf : flags leaf.1 <;>
    simp only [mixedInside, flaggedSlot, selectSlot, SourceProjectedTag.mixedInside,
      SourceProjectedTag.originalSlots, sourceSlots, PreliminarySampler.endpoints,
      SourceChildKernel.mixedSlots, SourceChildKernel.nativeSlots,
      ProjectedCardinality.projectedSlots, SourceChildKernel.ids,
      SourceClause.occurrenceVariable, SourceKeys.slot, hf, htree]

private theorem projection_family_heq
    {left right₁ right₂ : Slots branch (i + 1) → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (p₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hp : ∀ leaf a, HEq (p₁ leaf a) (p₂ leaf a)) : HEq p₁ p₂ := by
  subst right₂
  apply heq_of_eq
  funext leaf a
  exact eq_of_heq (hp leaf a)

private theorem mpr_heq {α β : Sort _} (h : α = β) (x : β) :
    HEq (Eq.mpr h x) x := by
  cases h
  rfl

private theorem flagged_occurrence_heq
    {e e' : SourceClause.Occurrence m} (h : e = e') (b : Bool) :
    HEq (flaggedProjection (SourceKeys.slot clauses (.clause e.1)) e.2 b)
      (flaggedProjection (SourceKeys.slot clauses (.clause e'.1)) e'.2 b) := by
  cases h
  rfl

private theorem child_projection_as_flagged (child : Fin (branch i))
    (s : SourceChildKernel.Source (m := m) (t := t) designated child)
    (b : Bool) (leaf : Slots branch i) (a : Fin t) :
    HEq (SourceChildKernel.projection clauses designated child s b leaf a)
      (flaggedProjection
        (SourceKeys.slot clauses (.clause (SourceChildKernel.tree designated child s leaf a).1))
        (SourceChildKernel.tree designated child s leaf a).2 b) := by
  cases b <;> rfl

theorem insideProjection_source :
    HEq (insideProjection (SourceProjectedTag.originalSlots clauses q) choices flags)
      (SourceProjectedTag.projection clauses designated q choices flags) := by
  apply projection_family_heq (mixedInside_source clauses designated q choices flags)
  intro leaf a
  have htree := tree_sources designated q choices leaf a
  have hcast : HEq (SourceProjectedTag.projection clauses designated q choices flags leaf a)
      (SourceChildKernel.projection clauses designated leaf.1
        (SourceQuestionKernelJoint.sources designated q choices leaf.1)
        (flags leaf.1) leaf.2 a) := by
    unfold SourceProjectedTag.projection
    dsimp only [id]
    exact mpr_heq _ _
  have hflagged := flagged_occurrence_heq clauses htree.symm (flags leaf.1)
  have hchild := child_projection_as_flagged clauses designated leaf.1
    (SourceQuestionKernelJoint.sources designated q choices leaf.1)
    (flags leaf.1) leaf.2 a
  exact hflagged.trans (hchild.symm.trans hcast.symm)

variable (originalQuestions : PreliminarySampler.Questions branch n t m)

theorem projectedSlots_source
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    projectedSlots rows hupper hij pref
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) k =
      StoppedProjectedExperiment.projectedSlots clauses rows hupper hij designated
        (originalQuestions, pref) k := by
  unfold projectedSlots StoppedProjectedExperiment.projectedSlots
  exact congrArg (CutSlotAssembly.fill (stoppedPath rows hupper hij pref k)
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)))
    (mixedInside_source clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij (originalQuestions, pref) k)
      k.2.1.1 k.2.1.2)

private theorem filled_projection_heq (p : Path branch n (i + 1))
    (outside : Slots branch n → Fin t → MixedSupport.Slot)
    (left right₁ right₂ : Slots branch (i + 1) → Fin t → MixedSupport.Slot)
    (hleft : CutSlotAssembly.fill p outside left = outside) (hr : right₁ = right₂)
    (p₁ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₁ leaf a))
    (p₂ : ∀ leaf a, MixedSupport.Projection (left leaf a) (right₂ leaf a))
    (hp : HEq p₁ p₂) :
    HEq (fun leaf a => CutProjectionAssembly.castProjection
        (congrFun (congrFun hleft leaf) a) rfl
        (CutProjectionAssembly.fillProjection p outside left right₁ p₁ leaf a))
      (fun leaf a => CutProjectionAssembly.castProjection
        (congrFun (congrFun hleft leaf) a) rfl
        (CutProjectionAssembly.fillProjection p outside left right₂ p₂ leaf a)) := by
  subst right₂
  have hp' : p₁ = p₂ := eq_of_heq hp
  subst p₂
  rfl

theorem projection_source
    (k : Inner (branch := branch) (n := n) (i := i) (j := j) (t := t) rows) :
    HEq (projection rows hupper hij pref
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) k)
      (StoppedProjectedExperiment.projection clauses rows hupper hij designated
        (originalQuestions, pref) k) := by
  exact filled_projection_heq (stoppedPath rows hupper hij pref k)
    (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions))
    (SourceProjectedTag.originalSlots clauses
      (StoppedProjectedExperiment.cutQuestions rows hupper hij (originalQuestions, pref) k))
    _ _ (StoppedProjectedExperiment.fill_native clauses rows hupper hij (originalQuestions, pref) k)
    (mixedInside_source clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij (originalQuestions, pref) k)
      k.2.1.1 k.2.1.2) _ _
    (insideProjection_source clauses designated
      (StoppedProjectedExperiment.cutQuestions rows hupper hij (originalQuestions, pref) k)
      k.2.1.1 k.2.1.2)

private theorem tagged_projection_heq {K : Type*}
    {left : Slots branch n → Fin t → MixedSupport.Slot}
    {right₁ right₂ : K → Slots branch n → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ k leaf a, MixedSupport.Projection (left leaf a) (right₁ k leaf a))
    (p₂ : ∀ k leaf a, MixedSupport.Projection (left leaf a) (right₂ k leaf a))
    (hp : ∀ k, HEq (p₁ k) (p₂ k)) : HEq p₁ p₂ := by
  subst right₂
  apply heq_of_eq
  funext k
  exact eq_of_heq (hp k)

private theorem projection_data_congr {K : Type*} {α : Sort*}
    {native : Slots branch n → Fin t → MixedSupport.Slot}
    {right₁ right₂ : K → Slots branch n → Fin t → MixedSupport.Slot}
    (hr : right₁ = right₂)
    (p₁ : ∀ k leaf a, MixedSupport.Projection (native leaf a) (right₁ k leaf a))
    (p₂ : ∀ k leaf a, MixedSupport.Projection (native leaf a) (right₂ k leaf a))
    (hp : HEq p₁ p₂)
    (f : (right : K → Slots branch n → Fin t → MixedSupport.Slot) →
      (∀ k leaf a, MixedSupport.Projection (native leaf a) (right k leaf a)) → α) :
    f right₁ p₁ = f right₂ p₂ := by
  subst right₂
  have hp' : p₁ = p₂ := eq_of_heq hp
  subst p₂
  rfl

theorem mark_source (κ : ℝ)
    (background : HierarchicalMatrixTable.Background (rows := rows)
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) (upper hupper pref))
    (X : HierarchicalFrozenTables.QuotientMatrix
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions))
      (upper hupper pref) (i + 1) background) :
    OriginalDecoderMark.mark (family rows repeats hupper hij pref hbranch hrows flag σ)
      (upper hupper pref) (i + 1) κ
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) background X ↔
    HierarchicalUsefulness.mark
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) (upper hupper pref) (i + 1)
      (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ (originalQuestions, pref)).original
      (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
        hbranch hrows flag σ (originalQuestions, pref)).arrays
      (HierarchicalAdviceExperiment.lowerEvent
        (StoppedProjectedExperiment.experiment clauses rows repeats hupper hij designated
          hbranch hrows flag σ (originalQuestions, pref))) κ ⟨background, X⟩ = true := by
  have hs := funext (projectedSlots_source rows hupper hij pref clauses designated originalQuestions)
  have hp := tagged_projection_heq hs _ _
    (projection_source rows hupper hij pref clauses designated originalQuestions)
  have hm := projection_data_congr hs _ _ hp (fun right proj =>
    let S := HierarchicalProjectedExperiment.experiment (rows := rows) (repeats := repeats)
      (sourceSlots clauses (PreliminarySampler.endpoints originalQuestions)) right proj
      (upper hupper pref) (i + 1) (lower rows hupper hij pref)
      (cut rows hupper hij pref) (direction rows hupper hij pref)
      (innerLaw rows hij hbranch hrows flag) σ
    HierarchicalUsefulness.mark S.slots S.upper S.lowerLevel S.original S.arrays
      (HierarchicalAdviceExperiment.lowerEvent S) κ ⟨background, X⟩)
  exact Iff.of_eq (congrArg (fun b : Bool => b = true) hm)

end Source

end
end PerfectCompleteness.SlotProjectedExperiment

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedStoppedMeetingEquality
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.FixedStoppedDirections.lowerDirectionNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedStoppedMeetingEquality

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.scalarFintype

local instance physicalLeftFintype_r99acde_2 {branch : Nat → Nat} {n t : Nat}
    (slots : Slots branch n → Fin t → MixedSupport.Slot) (upper : Nodes branch n) :
    Fintype (Module.Dual (ZMod 2) (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
private theorem nodeDirection_val_heq {branch rows : Nat → Nat} {n : Nat}
    (level : Fin n) (node other : PrefixTests.LevelNode branch level)
    (hn : node = other) (direction : PrefixTests.LevelDirection rows level) :
    HEq (PrefixTests.nodeDirection rows level node direction).val
      (PrefixTests.nodeDirection rows level other direction).val := by
  cases hn
  rfl

private theorem familyMeetingProbability_eq_of_useful
    {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
    {Sample : OriginalDecoderMark.SlotFamily branch plan.depth t → Type*}
    [∀ slots, Fintype (Sample slots)]
    (F : OriginalDecoderMark.Family branch (FixedRows.rows plan) plan.depth t Sample)
    (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
    (slots projected : Slots branch plan.depth → Fin t → MixedSupport.Slot)
    (projection : ∀ s k, MixedSupport.Projection (slots s k) (projected s k))
    (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)
    {Ω : Type*} [Fintype Ω] (original : FiniteDistribution Ω)
    (arrays : Ω → Arrays slots (FixedRows.rows plan)) (lowerEvent : Ω → Bool)
    (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
    (a : Block (FixedRows.rows plan) lower) (cut : OwnInputReference.Cut upper lower)
    (threshold : ℝ)
    (visible : HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan)
      upper lower A (FixedRows.repeats plan) cut)
    (huseful : ∀ background : HierarchicalMatrixTable.Background
        (rows := FixedRows.rows plan) slots upper,
      HierarchicalProjectedMeeting.useful slots upper lowerLevel background
          (F.original slots) (F.arrays slots) (F.lowerEvent slots) (InitialParameters.useful δ) =
        HierarchicalProjectedMeeting.useful slots upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ))
    (hthreshold : threshold = UpperParameterScalars.tau (InitialParameters.useful δ)
      plan.density plan.order (FixedRows.rows plan (Nodes.height upper))) :
    ProjectedMeetingTransport.familyMeetingProbability plan F σ slots projected projection
        upper lower lowerLevel A a cut threshold visible =
      HierarchicalProjectedRawMeeting.meetingProbability plan slots projected projection
        upper lower lowerLevel original arrays lowerEvent σ A a cut visible := by
  unfold ProjectedMeetingTransport.familyMeetingProbability
    HierarchicalProjectedRawMeeting.meetingProbability HierarchicalProjectedMeeting.leftLaw
  rw [huseful, hthreshold]

variable {δ : ℚ} {hδ : 0 < δ} (parameters : FixedParameters.Parameters δ hδ)
  (i j : Fin parameters.plan.depth) (hij : i < j) (input : List Bool)

variable (strategy : FixedPreliminaryGame.Strategy parameters input)

private theorem familyMeetingOnRaw_eq
    (sample : OriginalRaw parameters i j hij input) :
    familyMeetingOnRaw parameters i j hij input strategy sample =
      StoppedProjectedMeetingLaw.rawMeetingProbability parameters.plan
        (branch := FixedParameters.branch parameters)
        (t := FixedRows.sourceLength parameters.plan hδ)
        (FixedStoppedPhysicalLaw.clauses input) (Nat.succ_le_of_lt j.isLt) hij
        (FixedStoppedPhysicalLaw.designated parameters i)
        (fun k _ => FixedParameters.branch_pos parameters k)
        (FixedStoppedDecoderLaw.flag parameters i)
        (FixedStoppedDecoderLaw.labeling parameters input strategy) sample := by
  let F := FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy
    (sample.1.2, sample.2.2.1.1)
  let S := StoppedProjectedExperiment.experiment
    (FixedStoppedPhysicalLaw.clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i)
    (fun k _ => FixedParameters.branch_pos parameters k)
    (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
    (FixedStoppedDecoderLaw.flag parameters i)
    (FixedStoppedDecoderLaw.labeling parameters input strategy) sample.1
  have hmark (background : HierarchicalMatrixTable.Background
      (rows := FixedRows.rows parameters.plan) S.slots S.upper) :
      HierarchicalProjectedMeeting.useful S.slots S.upper (i.val + 1) background
        (F.original S.slots) (F.arrays S.slots) (F.lowerEvent S.slots)
        (InitialParameters.useful δ) =
      HierarchicalProjectedMeeting.useful S.slots S.upper (i.val + 1) background
        S.original S.arrays (HierarchicalAdviceExperiment.lowerEvent S)
        (InitialParameters.useful δ) := by
    funext X
    exact propext (SlotProjectedExperiment.mark_source
      (FixedRows.rows parameters.plan) (FixedRows.repeats parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1.2
      (fun k _ => FixedParameters.branch_pos parameters k)
      (StoppedProjectedMeetingLaw.rows_positive parameters.plan)
      (FixedStoppedDecoderLaw.flag parameters i)
      (FixedStoppedDecoderLaw.labeling parameters input strategy)
      (FixedStoppedPhysicalLaw.clauses input) (FixedStoppedPhysicalLaw.designated parameters i)
      sample.1.1 (InitialParameters.useful δ) background X)
  have hthreshold : FixedStoppedDecoderLaw.threshold parameters j =
      UpperParameterScalars.tau (InitialParameters.useful δ) parameters.plan.density
        parameters.plan.order (FixedRows.rows parameters.plan (Nodes.height S.upper)) := by
    simp only [FixedStoppedDecoderLaw.threshold, S,
      HierarchicalProjectedExperiment.experiment, StoppedProjectedExperiment.upper_height]
  exact familyMeetingProbability_eq_of_useful parameters.plan F
    (FixedStoppedDecoderLaw.labeling parameters input strategy) S.slots
    (StoppedProjectedExperiment.projectedSlots (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.projection (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) sample.1 sample.2.2.1)
    S.upper
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1) (i.val + 1)
    S.original S.arrays (HierarchicalAdviceExperiment.lowerEvent S) sample.2.1
    (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij sample.1 sample.2.2.1)
    (FixedStoppedDecoderLaw.threshold parameters j) sample.2.2.2.2 hmark hthreshold

private theorem direction_heq
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    HEq (FixedStoppedDecoderContext.direction parameters i j hij input sample.1)
      (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij
        (FixedStoppedNativeProjection.physicalSample parameters i j hij input sample).1
        (FixedStoppedNativeProjection.innerTag parameters i j hij input sample)) := by
  let physical := FixedStoppedNativeProjection.physicalSample parameters i j hij input sample
  let tag := FixedStoppedNativeProjection.innerTag parameters i j hij input sample
  have hlower := (StoppedCleanCutEquality.stopped_lower_eq (FixedRows.rows parameters.plan)
    (Nat.succ_le_of_lt j.isLt) hij physical.1 tag).symm
  have hnodes :
      (⟨CleanPhysicalDecoderLaw.lower
        (FixedStoppedNativeLaw.setup parameters i j hij input sample.1),
        CleanDecoderContext.lowerHeight
          (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
          (FixedStoppedDecoderContext.lowerIndex parameters i j hij input sample.1)⟩ :
        PrefixTests.LevelNode (FixedParameters.branch parameters) i) =
      ⟨StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
        (Nat.succ_le_of_lt j.isLt) hij physical.1 tag,
        StoppedProjectedExperiment.lower_height (FixedRows.rows parameters.plan)
          (Nat.succ_le_of_lt j.isLt) hij physical.1 tag⟩ :=
    Subtype.ext hlower
  exact nodeDirection_val_heq (rows := FixedRows.rows parameters.plan) i _ _ hnodes
    (sample.1.2.2.2.1 i)

private theorem cleanMeetingProbability_eq_familyOnRaw
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    cleanMeetingProbability parameters i j hij input strategy sample =
      familyMeetingOnRaw parameters i j hij input strategy
        (StoppedProjectedPhysicalAdvice.read
          (FixedStoppedPhysicalLaw.clauses input) (FixedRows.rows parameters.plan)
          (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
          (FixedStoppedPhysicalLaw.designated parameters i) parameters.plan.order
          (FixedStoppedNativeLaw.read parameters i j hij input sample)) := by
  let S := FixedStoppedNativeLaw.setup parameters i j hij input sample.1
  let physical := FixedStoppedNativeProjection.physicalSample parameters i j hij input sample
  let tag := FixedStoppedNativeProjection.innerTag parameters i j hij input sample
  let record := StoppedProjectedPhysicalAdvice.read
    (FixedStoppedPhysicalLaw.clauses input) (FixedRows.rows parameters.plan)
    (FixedRows.repeats parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
    (FixedStoppedPhysicalLaw.designated parameters i) parameters.plan.order physical
  exact ProjectedMeetingTransport.familyMeetingProbability_congr parameters.plan
    (FixedStoppedDecoderLaw.markFamily parameters i j hij input strategy sample.1.1)
    (FixedStoppedDecoderLaw.labeling parameters input strategy)
    (CleanNativeReplay.leftSlots S sample.2) (CleanNativeReplay.rightSlots S sample.2)
    (CleanPhysicalDecoderLaw.physicalProjection S sample.2)
    (FixedStoppedDecoderContext.upperNode parameters i j hij input sample.1)
    (CleanPhysicalDecoderLaw.lower S) (i.val + 1)
    (FixedStoppedDecoderContext.advice parameters i j hij input sample.1)
    (FixedStoppedDecoderContext.direction parameters i j hij input sample.1) S.cut
    (FixedStoppedDecoderLaw.threshold parameters j)
    (CleanPhysicalProjectedMeeting.visible S
      (LinearMap.ker (FixedStoppedDecoderContext.advice parameters i j hij input sample.1)) sample.2)
    (StoppedProjectedExperiment.nativeSlots (FixedStoppedPhysicalLaw.clauses input) physical.1)
    (StoppedProjectedExperiment.projectedSlots (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) physical.1 tag)
    (StoppedProjectedExperiment.lower (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag)
    (StoppedProjectedExperiment.projection (FixedStoppedPhysicalLaw.clauses input)
      (FixedRows.rows parameters.plan) (Nat.succ_le_of_lt j.isLt) hij
      (FixedStoppedPhysicalLaw.designated parameters i) physical.1 tag)
    (StoppedProjectedExperiment.direction (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag)
    (StoppedProjectedExperiment.cut (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag) record.2.2.2.2
    (FixedStoppedNativeProjection.leftSlots_eq parameters i j hij input sample)
    (FixedStoppedNativeProjection.rightSlots_eq parameters i j hij input sample)
    (StoppedCleanCutEquality.stopped_lower_eq (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag).symm
    (FixedStoppedNativeProjection.projection_heq parameters i j hij input sample)
    (direction_heq parameters i j hij input sample)
    (StoppedCleanCutEquality.stopped_cut_heq (FixedRows.rows parameters.plan)
      (Nat.succ_le_of_lt j.isLt) hij physical.1 tag).symm
    (FixedStoppedNativeTape.visible_heq parameters i j hij input sample).symm

private theorem cleanMeetingProbability_eq_physical
    (sample : FixedStoppedNativeLaw.Sample parameters i j hij input) :
    cleanMeetingProbability parameters i j hij input strategy sample =
      physicalMeetingProbability parameters i j hij input strategy sample :=
  (cleanMeetingProbability_eq_familyOnRaw parameters i j hij input strategy sample).trans
    (familyMeetingOnRaw_eq parameters i j hij input strategy _)

theorem native_probability_eq_expectation :
    (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.meeting parameters i j hij input) =
      (FixedStoppedNativeLaw.law parameters i j hij input).expectation
        (nativeMeetingProbability parameters i j hij input strategy) := by
  simp only [FixedStoppedDecoderLaw.law, DecoderFamilyLaw.law,
    DecoderFamilyLaw.fiberLaw, CleanDecoderPairLaw.pairLaw,
    CompletionSoundness.sigmaLaw_probability, FixedStoppedNativeLaw.law,
    CandidateCoupling.expectation_sigmaLaw, nativeMeetingProbability,
    FixedStoppedDecoderLaw.meeting, DecoderFamilyLaw.meeting]
  rfl

theorem meeting_probability_eq_expectedMeeting_oai :
    (FixedStoppedDecoderLaw.law parameters i j hij input strategy).probability
        (FixedStoppedDecoderLaw.meeting parameters i j hij input) =
      expectedMeeting parameters i j hij input strategy := by
  rw [native_probability_eq_expectation, native_expectation_eq_cleanMeeting]
  calc
    _ = (FixedStoppedNativeLaw.law parameters i j hij input).expectation
        (physicalMeetingProbability parameters i j hij input strategy) :=
      FiniteDistribution.expectation_congr _
        (cleanMeetingProbability_eq_physical parameters i j hij input strategy)
    _ = _ := physical_expectation_eq_expectedMeeting parameters i j hij input strategy

end
end PerfectCompleteness.FixedStoppedMeetingEquality

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedStoppedMeetingEquality.meeting_probability_eq_expectedMeeting_oai := @OAI.PerfectCompleteness.FixedStoppedMeetingEquality.meeting_probability_eq_expectedMeeting_oai
