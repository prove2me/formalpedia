-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.expectedMeeting_ge_prediction_difference
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:26.296489+00:00
-- url     : https://prove2.me/submissions/a5ffb624-9c78-4113-8f16-40b68777e4c0

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
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalProjectedRawPrediction_conditional_prediction_eq
import Theorems.Thm_OAI_PerfectCompleteness_RightDecoderAffineSuccess_coset_probability_lower

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PartitionsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedColumnSlice

noncomputable section

variable {𝕜 H H' W : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H] [AddCommGroup H'] [Module 𝕜 H']
  [AddCommGroup W] [Module 𝕜 W]
  (i : H' →ₗ[𝕜] H) (Z : Submodule 𝕜 (Module.Dual 𝕜 H))

theorem finrank_projectedColumns_le [FiniteDimensional 𝕜 Z] :
    Module.finrank 𝕜 (projectedColumns i Z) ≤ Module.finrank 𝕜 Z :=
  Submodule.finrank_map_le i.dualMap Z

end
end PerfectCompleteness.ProjectedColumnSlice

end

section

namespace PerfectCompleteness.PulledColumnSpace

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {H : Type*} [AddCommGroup H] [Module F2 H]

theorem finrank_pulled (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    Module.finrank F2 (pulled W C) = Module.finrank F2 C :=
  (pulledEquiv W C).finrank_eq.symm

variable [FiniteDimensional F2 H]

theorem card_pulled (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) :
    Nat.card (pulled W C) = 2 ^ Module.finrank F2 C := by
  rw [Module.natCard_eq_pow_finrank (K := F2), finrank_pulled]
  rw [show Nat.card F2 = 2 from Nat.card_zmod 2]

theorem card_candidates (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    Nat.card (Candidates W C center) = 2 ^ Module.finrank F2 C :=
  (Nat.card_congr (candidateEquiv W C center)).symm.trans (card_pulled W C)

theorem fintype_card_candidates (W : Submodule F2 H)
    (C : Submodule F2 (Module.Dual F2 (H ⧸ W))) (center : Module.Dual F2 H) :
    Fintype.card (Candidates W C center) = 2 ^ Module.finrank F2 C := by
  rw [← Nat.card_eq_fintype_card]
  exact card_candidates W C center

end
end PerfectCompleteness.PulledColumnSpace

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_Conditioning
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Conditioning of actual finite distributions and the selected-coordinate chain
rule used in parallel repetition. A normalized conditional distribution is only
constructed when the conditioning event has strictly positive probability.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators

noncomputable section

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

theorem probability_condition (μ : FiniteDistribution Ω) (given event : Ω → Bool)
    (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability event =
      μ.probability (fun x => given x && event x) / μ.probability given := by
  simp only [probability, condition, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hg : given x = true <;> by_cases he : event x = true <;> simp [hg, he]

@[simp] theorem probability_condition_given (μ : FiniteDistribution Ω)
    (given : Ω → Bool) (positive : 0 < μ.probability given) :
    (μ.condition given positive).probability given = 1 := by
  rw [μ.probability_condition]
  simpa only [Bool.and_self] using div_self (ne_of_gt positive)

end FiniteDistribution

end

end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FiniteListSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteListSampling

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

omit [DecidableEq A] in
theorem probability_ge_weight (μ : FiniteDistribution A) (event : A → Bool)
    (a : A) (ha : event a = true) : μ.weight a ≤ μ.probability event := by
  change μ.weight a ≤ ∑ x, if event x then μ.weight x else 0
  have h := Finset.single_le_sum
    (f := fun x : A => if event x then μ.weight x else 0)
    (fun x _ => by split; exact μ.nonnegative x; exact le_rfl) (Finset.mem_univ a)
  simpa only [ha, ite_true, if_true] using h

end
end PerfectCompleteness.FiniteListSampling

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LeftDecoder
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineFunctionalDependence.coefficientSum_apply _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.LeftDecoder

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open ClauseSupport MixedSupport

noncomputable section

section Affine

variable {V : Type*} [AddCommGroup V] [Module F2 V] [FiniteDimensional F2 V]

attribute [local instance] OAI.PerfectCompleteness.LeftDecoder.dualFintype
theorem affineLaw_weight (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center q : Module.Dual F2 V) :
    (affineLaw W C center).weight q =
      if q - center ∈ PulledColumnSpace.pulled W C then
        1 / (2 : ℝ) ^ Module.finrank F2 C else 0 := by
  have hweight : (affineLaw W C center).weight q =
      if q - center ∈ PulledColumnSpace.pulled W C then
        1 / (Fintype.card (PulledColumnSpace.Candidates W C center) : ℝ) else 0 := by
    let : Fintype {p : Module.Dual F2 V // p - center ∈ PulledColumnSpace.pulled W C} :=
      PulledColumnSpace.candidatesFintype W C center
    change (∑ p : {p : Module.Dual F2 V // p - center ∈ PulledColumnSpace.pulled W C},
      if p.val = q then
        1 / (Fintype.card (PulledColumnSpace.Candidates W C center) : ℝ) else 0) = _
    by_cases hq : q - center ∈ PulledColumnSpace.pulled W C
    · rw [ite_eq_left hq, Finset.sum_eq_single
        (⟨q, hq⟩ : {p : Module.Dual F2 V // p - center ∈ PulledColumnSpace.pulled W C})]
      · simp
      · intro p _ hp
        have hne : p.val ≠ q := fun heq => hp (Subtype.ext heq)
        simp [hne]
      · simp
    · rw [ite_eq_right hq]
      apply Finset.sum_eq_zero
      intro p _
      have hne : p.val ≠ q := fun heq => hq (heq ▸ p.property)
      simp [hne]
  simpa only [PulledColumnSpace.fintype_card_candidates, Nat.cast_pow, Nat.cast_ofNat]
    using hweight

theorem affineLaw_success_lower (W : Submodule F2 V)
    (C : Submodule F2 (Module.Dual F2 (V ⧸ W))) (center : Module.Dual F2 V)
    {r : Nat} (hC : Module.finrank F2 C ≤ r) (event : Module.Dual F2 V → Bool)
    (witness : ∃ q : PulledColumnSpace.Candidates W C center, event q.val = true) :
    1 / (2 : ℝ) ^ r ≤ (affineLaw W C center).probability event := by
  obtain ⟨q, hq⟩ := witness
  have hweight := FiniteListSampling.probability_ge_weight
    (affineLaw W C center) event q.val hq
  rw [affineLaw_weight, ite_eq_left q.property] at hweight
  exact (one_div_le_one_div_of_le (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hC)).trans hweight

end Affine


attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {n : Nat} {K Z : Type*} [AddCommGroup K] [Module F2 K]
  (slots : Fin n → Slot) (H : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (labeling : KeyStrategy.Strategy n)
  (W : Submodule F2 H) (s : (H ⧸ W) →ₗ[F2] H)
  (hs : W.mkQ.comp s = LinearMap.id)
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Z]
  (useful : (Module.Dual F2 (H ⧸ W) →ₗ[F2] K) → Prop)
  {r : Nat} {ρ : ℝ} {A : ManyGoodRows.RowMap K r}
  {U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2)}

omit [FiniteDimensional F2 K] [Fintype Z]

attribute [local instance] OAI.PerfectCompleteness.LeftDecoder.representativeDualFintype
theorem adviceLaw_of_good (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
    (U : Module.Dual F2 (H ⧸ W) →ₗ[F2] (Fin r → F2))
    (hgood : ManyGoodRows.GoodRow
      (RepresentativeMatrixTable.partialTable slots H other labeling W s useful) r ρ A U) :
    adviceLaw slots H other labeling W s hs useful r ρ A U =
      law slots H other labeling W s hs useful
        (ManyGoodRows.selectWitness
          (RepresentativeMatrixTable.partialTable slots H other labeling W s useful)
          r ρ A U hgood) := by
  simp only [adviceLaw, dite_eq_left hgood]


end

end PerfectCompleteness.LeftDecoder

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TupleIndexEmitterLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.UsefulMark

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω P : Type*} [Fintype Ω] [Fintype P]

theorem probability_eq_sum_fibers (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : Ω → Bool) : μ.probability event = ∑ z, lowerFiberMass μ p event z := by
  unfold lowerFiberMass FiniteDistribution.probability
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x <;> simp [he, eq_comm]

theorem probability_mark_eq_sum (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (mark : P → Bool) :
    μ.probability (fun x => L x && mark (p x)) =
      ∑ z, if mark z then lowerFiberMass μ p L z else 0 := by
  rw [probability_eq_sum_fibers μ p]
  apply Finset.sum_congr rfl
  intro z _
  unfold lowerFiberMass FiniteDistribution.probability
  by_cases hz : mark z = true
  · rw [ite_eq_left hz]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : p x = z <;> simp [hx, hz]
  · rw [ite_eq_right hz]
    apply Finset.sum_eq_zero
    intro x _
    by_cases hx : p x = z <;> simp [hx, hz]

end
end PerfectCompleteness.UsefulMark



namespace PerfectCompleteness.PositiveFiberMass

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Ω R : Type*} [Fintype Ω] [Fintype R]

omit [Fintype R] in
theorem goodRecord_iff (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (r : R) :
    goodRecord μ record J prediction ρ r = true ↔
      0 < jMass μ record J r ∧ ρ ≤ conditionalMatch μ record J prediction r := by
  simp only [goodRecord, decide_eq_true_eq]

omit [Fintype R] in
theorem jMass_nonneg (μ : FiniteDistribution Ω) (record : Ω → R)
    (J : Ω → Bool) (r : R) : 0 ≤ jMass μ record J r :=
  μ.probability_nonnegative _

omit [Fintype R] in
theorem matchMass_nonneg (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) : 0 ≤ matchMass μ record J prediction r :=
  μ.probability_nonnegative _

omit [Fintype R] in
theorem matchMass_le_jMass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) :
    matchMass μ record J prediction r ≤ jMass μ record J r := by
  apply μ.probability_mono
  intro x hx
  simp only [Bool.and_eq_true] at hx ⊢
  exact ⟨hx.1.1, hx.2⟩

omit [Fintype R] in
theorem matchMass_eq_zero (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (r : R) (hzero : jMass μ record J r = 0) :
    matchMass μ record J prediction r = 0 :=
  le_antisymm ((matchMass_le_jMass μ record J prediction r).trans_eq hzero)
    (matchMass_nonneg μ record J prediction r)

omit [Fintype R] in
theorem matchMass_le_of_not_goodRecord (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (r : R)
    (hbad : goodRecord μ record J prediction ρ r ≠ true) :
    matchMass μ record J prediction r ≤ ρ * jMass μ record J r := by
  by_cases hpos : 0 < jMass μ record J r
  · have hlt : conditionalMatch μ record J prediction r < ρ := by
      apply lt_of_not_ge
      intro hρ
      exact hbad ((goodRecord_iff μ record J prediction ρ r).mpr ⟨hpos, hρ⟩)
    change matchMass μ record J prediction r / jMass μ record J r < ρ at hlt
    exact ((div_lt_iff₀ hpos).mp hlt).le
  · have hzero : jMass μ record J r = 0 :=
      le_antisymm (le_of_not_gt hpos) (jMass_nonneg μ record J r)
    rw [matchMass_eq_zero μ record J prediction r hzero, hzero, mul_zero]

omit [Fintype R] in
theorem fiber_difference_le_good_mass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (hρ : 0 ≤ ρ) (r : R) :
    matchMass μ record J prediction r - ρ * jMass μ record J r ≤
      if goodRecord μ record J prediction ρ r then jMass μ record J r else 0 := by
  by_cases hgood : goodRecord μ record J prediction ρ r = true
  · rw [ite_eq_left hgood]
    have hmatch := matchMass_le_jMass μ record J prediction r
    have hproduct := mul_nonneg hρ (jMass_nonneg μ record J r)
    linarith
  · rw [ite_eq_right hgood]
    exact sub_nonpos.mpr (matchMass_le_of_not_goodRecord μ record J prediction ρ r hgood)

theorem sum_jMass (μ : FiniteDistribution Ω) (record : Ω → R) (J : Ω → Bool) :
    (∑ r, jMass μ record J r) = μ.probability J :=
  (UsefulMark.probability_eq_sum_fibers μ record J).symm

theorem sum_matchMass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) :
    (∑ r, matchMass μ record J prediction r) =
      μ.probability (fun x => J x && prediction x) :=
  (UsefulMark.probability_eq_sum_fibers μ record (fun x => J x && prediction x)).symm

theorem difference_eq_sum (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) :
    μ.probability (fun x => J x && prediction x) - ρ * μ.probability J =
      ∑ r, (matchMass μ record J prediction r - ρ * jMass μ record J r) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_matchMass, sum_jMass]

theorem difference_le_good_mass (μ : FiniteDistribution Ω) (record : Ω → R)
    (J prediction : Ω → Bool) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    μ.probability (fun x => J x && prediction x) - ρ * μ.probability J ≤
      μ.probability (fun x => J x && goodRecord μ record J prediction ρ (record x)) := by
  rw [difference_eq_sum μ record J prediction ρ,
    UsefulMark.probability_mark_eq_sum μ record J (goodRecord μ record J prediction ρ)]
  apply Finset.sum_le_sum
  intro r _
  exact fiber_difference_le_good_mass μ record J prediction ρ hρ r

end
end PerfectCompleteness.PositiveFiberMass



namespace PerfectCompleteness.UsefulAdvice

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UsefulMark

noncomputable section

variable {Ω P : Type*} [Fintype Ω] [Fintype P]

variable {A : Type*} [Fintype A]

theorem product_probability_advice_first (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution A) (event : Ω × A → Bool) :
    (μ.product ν).probability event =
      ν.expectation (fun a => μ.probability (fun x => event (x, a))) := by
  calc
    _ = ∑ x, ∑ a, if event (x, a) then μ.weight x * ν.weight a else 0 := by
      simp only [FiniteDistribution.probability, FiniteDistribution.product,
        Fintype.sum_prod_type]
    _ = ∑ a, ∑ x, if event (x, a) then μ.weight x * ν.weight a else 0 :=
      Finset.sum_comm
    _ = _ := by
      simp only [FiniteDistribution.expectation, FiniteDistribution.probability,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro x _
      by_cases he : event (x, a) = true <;> simp [he, mul_comm]

end
end PerfectCompleteness.UsefulAdvice



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_AffineDecoderMeeting
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.AffineDecoderMeeting

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section Product

variable {L R : Type*} [Fintype L] [Fintype R]

theorem product_probability_lower
    (left : FiniteDistribution L) (right : FiniteDistribution R)
    (event : L × R → Bool) (good : R → Bool) (p : ℝ)
    (hpoint : ∀ y, good y = true →
      p ≤ left.probability (fun x => event (x, y))) :
    p * right.probability good ≤ (left.product right).probability event := by
  rw [UsefulAdvice.product_probability_advice_first]
  change p * (∑ y, if good y then right.weight y else 0) ≤
    ∑ y, right.weight y * left.probability (fun x => event (x, y))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  by_cases hy : good y = true
  · rw [ite_eq_left hy, mul_comm p]
    exact mul_le_mul_of_nonneg_left (hpoint y hy) (right.nonnegative y)
  · rw [ite_eq_right hy, mul_zero]
    exact mul_nonneg (right.nonnegative y) (left.probability_nonnegative _)

end Product

section Algebra

variable {H H' : Type*} [AddCommGroup H] [Module F2 H]
  [AddCommGroup H'] [Module F2 H']
  (i : H' →ₗ[F2] H) (B : Submodule F2 H)
  (C : Submodule F2 (Module.Dual F2 (H ⧸ B)))
  (center : Module.Dual F2 H)

theorem exists_candidate_of_mem_nativeCoset (decoded : Module.Dual F2 H')
    (hdecoded : decoded - nativeCenter i center ∈ nativeQ i B C) :
    ∃ q : PulledColumnSpace.Candidates B C center, i.dualMap q.val = decoded := by
  obtain ⟨q, hq, heq⟩ := Submodule.mem_map.mp hdecoded
  refine ⟨PulledColumnSpace.candidateEquiv B C center ⟨q, hq⟩, ?_⟩
  change i.dualMap (center + q) = decoded
  rw [map_add, heq]
  change i.dualMap center + (decoded - i.dualMap center) = decoded
  abel

end Algebra


variable {H H' : Type*} [AddCommGroup H] [Module F2 H]
  [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H] [FiniteDimensional F2 H']

variable (i : H' →ₗ[F2] H) (B : Submodule F2 H)
  (C : Submodule F2 (Module.Dual F2 (H ⧸ B)))
  (center : Module.Dual F2 H)

local instance leftDualFintype_ra46bd4_1 : Fintype (Module.Dual F2 H) :=
  LeftDecoder.dualFintype (V := H)
local instance nativeDualFintype_ra46bd4_1 : Fintype (Module.Dual F2 H') :=
  LeftDecoder.dualFintype (V := H')
omit [FiniteDimensional F2 H'] in
theorem native_point_probability_lower {r : Nat}
    (hC : Module.finrank F2 C ≤ r) (decoded : Module.Dual F2 H')
    (hdecoded : decoded - nativeCenter i center ∈ nativeQ i B C) :
    1 / (2 : ℝ) ^ r ≤ (LeftDecoder.affineLaw B C center).probability
      (fun q => decide (i.dualMap q = decoded)) := by
  apply LeftDecoder.affineLaw_success_lower B C center hC
  obtain ⟨q, hq⟩ := exists_candidate_of_mem_nativeCoset i B C center decoded hdecoded
  exact ⟨q, decide_eq_true hq⟩


end
end PerfectCompleteness.AffineDecoderMeeting

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
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.TensorSelectedSlice

noncomputable section

open scoped Classical TensorProduct
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {K H H' Y : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H] [AddCommGroup H'] [Module F2 H']
  [FiniteDimensional F2 H'] [FiniteDimensional F2 H] [FiniteDimensional F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  (i : H' →ₗ[F2] H) (W : Submodule F2 K) (B : Submodule F2 H)

variable (f : (Module.Dual F2 (H ⧸ B) →ₗ[F2] K) → Option Y)
  (r : Nat) (ρ : ℝ) (A : ManyGoodRows.RowMap K r)
  (X₀ : Module.Dual F2 H →ₗ[F2] K)

omit [FiniteDimensional F2 H'] [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem columnSpace_eq_sequential_maps
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    columnSpace i B f r ρ A X₀ hgood =
      ((witness B f r ρ A X₀ hgood).columnSpace.map B.mkQ.dualMap).map i.dualMap := by
  unfold columnSpace ProjectedColumnSlice.projectedColumns
  exact Submodule.map_comp B.mkQ.dualMap i.dualMap _

omit [FiniteDimensional F2 H'] [FiniteDimensional F2 K] [Fintype Y] in
theorem finrank_columnSpace_le
    (hgood : ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀))) :
    Module.finrank F2 (columnSpace i B f r ρ A X₀ hgood) ≤ r :=
  (ProjectedColumnSlice.finrank_projectedColumns_le (B.mkQ.comp i)
    (witness B f r ρ A X₀ hgood).columnSpace).trans
      (witness B f r ρ A X₀ hgood).column_count

variable (hW : W ≤ LinearMap.ker A)

include hW

omit [FiniteDimensional F2 H] [FiniteDimensional F2 K] [Fintype Y] in
theorem J_false_of_not_good
    (hbad : ¬ ManyGoodRows.GoodRow f r ρ A (A.comp (MatrixRowQuotient.projectMatrix B X₀)))
    (T : W ⊗[F2] H') :
    GoodAdviceEvents.J f r ρ (A, projectedMatrix i W B X₀ T) = false := by
  change GoodAdviceEvents.selectedColumn f r ρ A
    (A.comp (projectedMatrix i W B X₀ T)) (projectedMatrix i W B X₀ T) = false
  unfold GoodAdviceEvents.selectedColumn
  have hrow : A.comp (projectedMatrix i W B X₀ T) =
      A.comp (MatrixRowQuotient.projectMatrix B X₀) :=
    TensorRowAdvice.rowAdvice_projectMatrix i W A hW B X₀ T
  rw [hrow]
  exact dite_eq_right hbad

end
end PerfectCompleteness.TensorSelectedSlice



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_TensorSliceDimension
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.TensorSliceDimension

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section GeneralEquationSpace

variable {Q W : Type*} [AddCommGroup Q] [Module F2 Q]
  [AddCommGroup W] [Module F2 W]
  [FiniteDimensional F2 Q] [FiniteDimensional F2 W]

theorem linearMap_finrank_le {r ℓ : Nat}
    (hQ : Module.finrank F2 Q ≤ r) (hW : Module.finrank F2 W ≤ ℓ) :
    Module.finrank F2 (Q →ₗ[F2] W) ≤ r * ℓ := by
  rw [Module.finrank_linearMap]
  exact Nat.mul_le_mul hQ hW

end GeneralEquationSpace

variable {H : Type*} [AddCommGroup H] [Module F2 H] [FiniteDimensional F2 H]
  {ℓ : Nat} (W : Submodule F2 (Fin ℓ → F2))
  (Q : Submodule F2 (Module.Dual F2 H))

theorem row_finrank_le : Module.finrank F2 W ≤ ℓ := by
  simpa only [Module.finrank_fin_fun] using (Submodule.finrank_le W)

theorem equation_finrank_le {r : Nat} (hQ : Module.finrank F2 Q ≤ r) :
    Module.finrank F2 (Q →ₗ[F2] W) ≤ r * ℓ :=
  linearMap_finrank_le (Q := Q) (W := W) hQ (row_finrank_le W)

end
end PerfectCompleteness.TensorSliceDimension

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatentSupportLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSamplerBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler QuarterBalance
open RecursiveSamplerBiasAlgebra RecursiveSamplerBiasProducts

noncomputable section

universe u

variable {branch : Nat → Nat} {n m : Nat}

theorem repetitionsBalanced_of_six_le (repeats : Nat → Nat)
    (hrep : ∀ k : Nat, 6 ≤ repeats (k + 1)) : RepetitionsBalanced repeats := by
  intro k
  calc
    (7 / 8 : ℝ) ^ repeats (k + 1) ≤ (7 / 8 : ℝ) ^ 6 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (hrep k)
    _ ≤ 1 / 2 := by norm_num

end
end PerfectCompleteness.RecursiveSamplerBias

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalDecoderMeetingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalFixedDecoderMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

theorem kernel_finrank_ge {ℓ r : Nat} (A : ManyGoodRows.RowMap (Fin ℓ → F2) r) :
    ℓ - r ≤ Module.finrank F2 (LinearMap.ker A) := by
  have hrange : Module.finrank F2 (LinearMap.range A) ≤ r := by
    simpa only [Module.finrank_fin_fun] using (Submodule.finrank_le (LinearMap.range A))
  have hdim := LinearMap.finrank_range_add_finrank_ker A
  simp only [Module.finrank_fin_fun] at hdim
  change Module.finrank F2 (LinearMap.range A) + Module.finrank F2 (LinearMap.ker A) = ℓ at hdim
  omega

variable {δ : ℚ} (plan : FixedRows.Plan δ)

theorem repetitionsBalanced : RecursiveSamplerBias.RepetitionsBalanced (FixedRows.repeats plan) :=
  RecursiveSamplerBias.repetitionsBalanced_of_six_le (FixedRows.repeats plan)
    (fun k => plan.repeats_min (FixedRows.rows plan (k + 1)))

theorem slice_error (height : Nat) :
    (7 / 8 : ℝ) ^ FixedRows.repeats plan height ≤
      h plan.order (FixedRows.rows plan height) / 2 :=
  (plan.repeats_error (FixedRows.rows plan height)).trans (min_le_left _ _)

theorem list_error (height : Nat) :
    (7 / 8 : ℝ) ^ FixedRows.repeats plan height ≤
      tau (InitialParameters.useful δ) plan.density plan.order (FixedRows.rows plan height) ^ 2 / 2 :=
  (plan.repeats_error (FixedRows.rows plan height)).trans (min_le_right _ _)

theorem kernel_excluded (height : Nat)
    (A : ManyGoodRows.RowMap (Fin (FixedRows.rows plan height) → F2) plan.order) :
    1 / (2 : ℝ) ^ Module.finrank F2 (LinearMap.ker A) <
      rhoPred (InitialParameters.useful δ) plan.density / 8 := by
  have hker := kernel_finrank_ge A
  apply (one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 2) hker).trans_lt
  simpa only [FixedRows.rows, DescendingRows.treeRows] using
    plan.rows_correction (plan.depth - height)

end
end PerfectCompleteness.HierarchicalFixedDecoderMeeting

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
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutNativeForms.formCast_apply _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DescriptorProjectionMachine.outputWords_length _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_count _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_current _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_extra _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_output _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_remaining _root_.OAI.PerfectCompleteness.ExactTargetOdometer.nativeTapes_table _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.selectRows_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutDecoderForm.form_apply _root_.OAI.PerfectCompleteness.LowerCutFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutPair.selected_second _root_.OAI.PerfectCompleteness.LowerCutPairBackground.observe_fresh _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinateEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutSingleFiberDisintegration.coordinates_complement _root_.OAI.PerfectCompleteness.LowerCutUniformCoordinates.sampleEquiv_apply _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.NormalizedTarget.parsedVariableIDs_eq _root_.OAI.PerfectCompleteness.NormalizedTarget.tupleQuestion_digits _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_refl _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_below _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_exterior _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_lowerCall _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.splitTape_step_rootCall _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.nodeScalarEquiv_apply _root_.OAI.PerfectCompleteness.ProjectedFiberBackground.scalarEquiv_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceIDs_tuple _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.SlotProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inl _root_.OAI.PerfectCompleteness.SourceChildKernelLaw.physical_inr _root_.OAI.PerfectCompleteness.SourceChildMarkedLaw.observe_mask _root_.OAI.PerfectCompleteness.SourceChildNativeLaw.pullback_false _root_.OAI.PerfectCompleteness.SourcePhysicalChildExpectation.observe_flags _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_fst _root_.OAI.PerfectCompleteness.SourcePhysicalTaggedChildren.observe_snd _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_apply _root_.OAI.PerfectCompleteness.SourceProjectedTag.sourceFlagEquiv_symm_apply _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_at_cut _root_.OAI.PerfectCompleteness.SourceQuestionCutSplit.join_outside _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceQuestionKernelJoint.sources_eq_join _root_.OAI.PerfectCompleteness.SourceQuestionPositionSplit.questions_join _root_.OAI.PerfectCompleteness.SourceQuestionRawSwap.raw_apply _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.StoppedCleanGeometry.lowerHeight _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.lower_height _root_.OAI.PerfectCompleteness.StoppedProjectedExperiment.upper_height _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
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
local instance valueFintype_ra46bd4_1 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
theorem columnSpace_eq_pulled
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    columnSpace originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      ((witness originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace.map
        (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background).mkQ.dualMap).map
        (ProjectedNodeEmbedding.intoOriginal projection upper).dualMap :=
  TensorSelectedSlice.columnSpace_eq_sequential_maps (ProjectedNodeEmbedding.intoOriginal projection upper)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) hgood

theorem finrank_columnSpace_le
    (hgood : VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    Module.finrank F2
      (columnSpace originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) ≤ r :=
  TensorSelectedSlice.finrank_columnSpace_le (ProjectedNodeEmbedding.intoOriginal projection upper)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) hgood

theorem J_false_of_not_good
    (hbad : ¬ VisibleGood originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (T : HiddenTensor projectedSlots upper A) :
    J originalSlots projectedSlots projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = false :=
  TensorSelectedSlice.J_false_of_not_good (ProjectedNodeEmbedding.intoOriginal projection upper) (LinearMap.ker A)
    (HierarchicalFrozenTables.knownRows originalSlots upper lowerLevel background)
    (table originalSlots upper lowerLevel background original arrays lowerEvent κ σ)
    r ρ A (visibleMatrix originalSlots projectedSlots projection upper A known) le_rfl hbad T

end
end PerfectCompleteness.HierarchicalProjectedSlice


namespace PerfectCompleteness.HierarchicalProjectedMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays HierarchicalProjectedSlice
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lowerEvent : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  {r : Nat} (ρ : ℝ) (A : ManyGoodRows.RowMap (Block rows upper) r)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projected upper)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedMeeting.rowSpaceFintype
local instance valueFintype_ra46bd4_2 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.HierarchicalProjectedMeeting.upperDualFintype
theorem leftLaw_eq_affine
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    leftLaw slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known =
      LeftDecoder.affineLaw
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace
        (correction slots upper lowerLevel background
          (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) := by
  have h := LeftDecoder.adviceLaw_of_good (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background) σ
      (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
      (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
      (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background)
      (useful slots upper lowerLevel background original arrays lowerEvent κ) r ρ A
      (A.comp (MatrixRowQuotient.projectMatrix
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (visibleMatrix slots projected projection upper A known))) hgood
  dsimp only [leftLaw, HierarchicalLeftDecoder.adviceLaw, LeftDecoder.law, LeftDecoder.center,
    HierarchicalProjectedSlice.witness, TensorSelectedSlice.witness, HierarchicalProjectedSlice.correction,
    HierarchicalProjectedSlice.table, HierarchicalUsefulness.table, HierarchicalFrozenTables.table,
    useful] at h ⊢
  exact h

theorem columnSpace_eq_nativeQ
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      AffineDecoderMeeting.nativeQ (ProjectedNodeEmbedding.intoOriginal projection upper)
        (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
        (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace :=
  HierarchicalProjectedSlice.columnSpace_eq_pulled slots projected projection upper lowerLevel background
    original arrays lowerEvent κ σ ρ A known hgood

theorem nativeCorrection_eq_nativeCenter
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known) :
    nativeCorrection slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood =
      AffineDecoderMeeting.nativeCenter (ProjectedNodeEmbedding.intoOriginal projection upper)
        (correction slots upper lowerLevel background
          (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value) := rfl

variable (lower : Nodes branch n) (a : Block rows lower)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper lower)
  (input : OwnInputReference.Input projected rows upper lower (LinearMap.ker A) a)

theorem meeting_probability_ge_coset
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (threshold : ℝ) :
    (1 / (2 : ℝ) ^ r) *
        (RightDecoder.law projected rows upper lower (LinearMap.ker A) a repeats cut σ input threshold).probability
          (fun decoded => decide (decoded -
            nativeCorrection slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood ∈
            columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)) ≤
      ((leftLaw slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known).product
        (RightDecoder.law projected rows upper lower (LinearMap.ker A) a repeats cut σ input threshold)).probability
          (fun pair => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap pair.1 = pair.2)) := by
  rw [leftLaw_eq_affine slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood]
  apply AffineDecoderMeeting.product_probability_lower
  intro decoded hdecoded
  have bound := AffineDecoderMeeting.native_point_probability_lower (ProjectedNodeEmbedding.intoOriginal projection upper)
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).columnSpace
    (correction slots upper lowerLevel background
      (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).value)
    (witness slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood).column_count decoded (by
      have hd := of_decide_eq_true hdecoded
      simpa only [columnSpace_eq_nativeQ slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood,
        nativeCorrection_eq_nativeCenter slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood]
        using hd)
  convert bound using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  funext candidate
  exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl

theorem meeting_probability_lower
    (hgood : VisibleGood slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known)
    (hne : ∃ T, J slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known T = true)
    (ρpred h₀ : ℝ) (hρpred : 0 < ρpred) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hslice : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hlist : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ (ρpred * h₀ / 4) ^ 2 / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 (LinearMap.ker A) < ρpred / 8)
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ (r * rows (Nodes.height upper)))
    (hmatch : ρpred ≤ RightDecoderWitness.conditionalMatch projected rows upper lower
      (LinearMap.ker A) a repeats cut σ input
      (columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (target slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne)
      (nativeCorrection slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
      (visibleOffset slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)) :
    (1 / (2 : ℝ) ^ r) *
        ((ρpred * h₀ / 4) ^ 2 / (2 * (2 : ℝ) ^ rows (Nodes.height upper))) ≤
      ((leftLaw slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known).product
        (RightDecoder.law projected rows upper lower (LinearMap.ker A) a repeats cut σ input
          (ρpred * h₀ / 4))).probability
          (fun pair => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap pair.1 = pair.2)) := by
  have hdimension := TensorSliceDimension.equation_finrank_le (LinearMap.ker A)
    (columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    (HierarchicalProjectedSlice.finrank_columnSpace_le slots projected projection upper lowerLevel background
      original arrays lowerEvent κ σ ρ A known hgood)
  have hsize' : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2
      ((columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) →ₗ[F2]
        LinearMap.ker A) :=
    hsize.trans (one_div_pow_le_one_div_pow_of_le (by norm_num : (1 : ℝ) ≤ 2) hdimension)
  have hright := RightDecoderAffineSuccess.coset_probability_lower projected rows upper lower
    (LinearMap.ker A) a repeats cut σ input ρpred h₀ hρpred hh₀ hrep hslice hlist hexcluded
    (columnSpace slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    hsize'
    (target slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood hne)
    (nativeCorrection slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood)
    (visibleOffset slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known hgood) hmatch
  exact (mul_le_mul_of_nonneg_left hright
    (div_nonneg zero_le_one (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) r))).trans
      (meeting_probability_ge_coset slots projected projection upper lowerLevel background original arrays lowerEvent κ σ ρ A known
        lower a repeats cut input hgood (ρpred * h₀ / 4))

end
end PerfectCompleteness.HierarchicalProjectedMeeting


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
local instance valueFintype_ra46bd4_3 : Fintype
    (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
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

theorem selection_of_positive
    (externalLaw : FiniteDistribution (OwnInputReference.Exterior projectedSlots rows upper lower))
    (v : Visible projectedSlots rows upper lower A repeats cut)
    (positive : 0 <
      (OwnInputReference.rawLaw projectedSlots rows upper lower (LinearMap.ker A) repeats cut externalLaw).probability
        (given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v)) :
    VisibleGood originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ A repeats cut v ∧
      ∃ T, tensorJ originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v T = true := by
  have hex : ∃ sample, given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
      A repeats cut v sample = true := by
    by_contra hnone
    have hfalse : given originalSlots projectedSlots projection rows upper lower lowerLevel original originalArrays lowerEvent κ σ ρ
        A repeats cut v = fun _ => false := by
      funext sample
      exact Bool.eq_false_iff.mpr (fun hs => hnone ⟨sample, hs⟩)
    rw [hfalse, FiniteDistribution.probability_false] at positive
    exact (lt_irrefl 0) positive
  obtain ⟨sample, hs⟩ := hex
  have hp := Bool.and_eq_true_iff.mp hs
  have hv : sample.2 = v := @of_decide_eq_true _ _ hp.2
  have ht := hp.1
  rw [rawJ_eq_tensorJ, hv] at ht
  refine ⟨?_, hidden projectedSlots rows upper lower A repeats cut sample, ht⟩
  by_contra hbad
  have hfalse := HierarchicalProjectedSlice.J_false_of_not_good originalSlots projectedSlots projection upper lowerLevel
    (visibleBackground originalSlots projectedSlots projection rows upper lower A repeats cut v)
    original originalArrays lowerEvent κ σ ρ A (known projectedSlots rows upper lower A repeats cut v)
    hbad (hidden projectedSlots rows upper lower A repeats cut sample)
  exact Bool.noConfusion (hfalse.symm.trans ht)

end
end PerfectCompleteness.HierarchicalProjectedRawPrediction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedComparisonErrorsLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalFixedProjectedMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays HierarchicalProjectedSlice
open UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) (hδ : 0 < δ)
  {branch : Nat → Nat} {t : Nat}
  (slots projected : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background
    (rows := FixedRows.rows plan) slots upper)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) → NodeEmbedding.NodeH projected upper)
  (lower : Nodes branch plan.depth) (a : Block (FixedRows.rows plan) lower)
  (cut : OwnInputReference.Cut upper lower)
  (input : OwnInputReference.Input projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a)

include hδ

local instance rowSpaceFintype_ra46bd4_1 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance valueFintype_ra46bd4_4 : Fintype
    (Block (FixedRows.rows plan) upper ×
      HierarchicalMatrixTable.SideOutput (rows := FixedRows.rows plan) upper) :=
  Fintype.ofFinite _
local instance upperDualFintype_ra46bd4_1 : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
theorem meeting_probability_lower
    (hgood : VisibleGood slots projected projection upper lowerLevel background
      original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known)
    (hne : ∃ T, J slots projected projection upper lowerLevel background
      original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known T = true)
    (hmatch : rhoPred (InitialParameters.useful δ) plan.density ≤
      RightDecoderWitness.conditionalMatch projected (FixedRows.rows plan) upper lower
        (LinearMap.ker A) a (FixedRows.repeats plan) cut σ input
        (columnSpace slots projected projection upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known hgood)
        (target slots projected projection upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known hgood hne)
        (nativeCorrection slots projected projection upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known hgood)
        (visibleOffset slots projected projection upper lowerLevel background
          original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known hgood)) :
    (1 / (2 : ℝ) ^ plan.order) *
        (tau (InitialParameters.useful δ) plan.density plan.order
          (FixedRows.rows plan (Nodes.height upper)) ^ 2 /
            (2 * (2 : ℝ) ^ FixedRows.rows plan (Nodes.height upper))) ≤
      ((HierarchicalProjectedMeeting.leftLaw slots projected projection upper lowerLevel
        background original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known).product
        (RightDecoder.law projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
          (FixedRows.repeats plan) cut σ input
          (tau (InitialParameters.useful δ) plan.density plan.order
            (FixedRows.rows plan (Nodes.height upper))))).probability
          (fun pair => decide ((ProjectedNodeEmbedding.intoOriginal projection upper).dualMap
            pair.1 = pair.2)) := by
  simpa only [UpperParameterScalars.tau] using
    (HierarchicalProjectedMeeting.meeting_probability_lower slots projected projection upper lowerLevel
      background original arrays lowerEvent (InitialParameters.useful δ) σ plan.density A known
      lower a (FixedRows.repeats plan) cut input hgood hne
      (rhoPred (InitialParameters.useful δ) plan.density)
      (h plan.order (FixedRows.rows plan (Nodes.height upper)))
      (rhoPred_pos (InitialParameters.useful_pos hδ) plan.density_pos)
      (h_pos plan.order (FixedRows.rows plan (Nodes.height upper)))
      (HierarchicalFixedDecoderMeeting.repetitionsBalanced plan)
      (HierarchicalFixedDecoderMeeting.slice_error plan (Nodes.height upper))
      (HierarchicalFixedDecoderMeeting.list_error plan (Nodes.height upper))
      (HierarchicalFixedDecoderMeeting.kernel_excluded plan (Nodes.height upper) A)
      le_rfl hmatch)

end
end PerfectCompleteness.HierarchicalFixedProjectedMeeting

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedRawMeeting
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalProjectedRawMeeting

noncomputable section

open scoped Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays
open UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype
attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  (slots projected : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω)
  (originalArrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower)
  (cut : OwnInputReference.Cut upper lower)
  (v : HierarchicalProjectedRawPrediction.Visible projected (FixedRows.rows plan) upper lower A
    (FixedRows.repeats plan) cut)

local instance rowSpaceFintype_ra46bd4_2 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance valueFintype_ra46bd4_5 : Fintype
    (Block (FixedRows.rows plan) upper ×
      HierarchicalMatrixTable.SideOutput (rows := FixedRows.rows plan) upper) :=
  Fintype.ofFinite _
local instance upperDualFintype_ra46bd4_2 : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
theorem meetingProbability_nonneg :
    0 ≤ meetingProbability plan slots projected projection upper lower lowerLevel
      original originalArrays lowerEvent σ A a cut v :=
  FiniteDistribution.probability_nonnegative _ _

theorem meeting_probability_lower (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower))
    (positive : 0 <
      (OwnInputReference.rawLaw projected (FixedRows.rows plan) upper lower (LinearMap.ker A)
        (FixedRows.repeats plan) cut externalLaw).probability
        (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan)
          upper lower lowerLevel original originalArrays lowerEvent (InitialParameters.useful δ)
          σ plan.density A (FixedRows.repeats plan) cut v))
    (hprediction : rhoPred (InitialParameters.useful δ) plan.density ≤
      ((OwnInputReference.rawLaw projected (FixedRows.rows plan) upper lower (LinearMap.ker A)
        (FixedRows.repeats plan) cut externalLaw).condition
        (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan)
          upper lower lowerLevel original originalArrays lowerEvent (InitialParameters.useful δ)
          σ plan.density A (FixedRows.repeats plan) cut v) positive).probability
        (HierarchicalProjectedRawPrediction.rawPrediction slots projected projection (FixedRows.rows plan)
          upper lower lowerLevel original originalArrays lowerEvent (InitialParameters.useful δ)
          σ plan.density A (FixedRows.repeats plan) cut a)) :
    (1 / (2 : ℝ) ^ plan.order) *
        (tau (InitialParameters.useful δ) plan.density plan.order
          (FixedRows.rows plan (Nodes.height upper)) ^ 2 /
            (2 * (2 : ℝ) ^ FixedRows.rows plan (Nodes.height upper))) ≤
      meetingProbability plan slots projected projection upper lower lowerLevel
        original originalArrays lowerEvent σ A a cut v := by
  obtain ⟨hgood, hne⟩ := HierarchicalProjectedRawPrediction.selection_of_positive
    slots projected projection (FixedRows.rows plan) upper lower lowerLevel
    original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
    (FixedRows.repeats plan) cut externalLaw v positive
  unfold meetingProbability
  apply HierarchicalFixedProjectedMeeting.meeting_probability_lower plan hδ
    slots projected projection upper lowerLevel
    (HierarchicalProjectedRawPrediction.visibleBackground slots projected projection
      (FixedRows.rows plan) upper lower A (FixedRows.repeats plan) cut v)
    original originalArrays lowerEvent σ A
    (HierarchicalProjectedRawPrediction.known projected (FixedRows.rows plan) upper lower A
      (FixedRows.repeats plan) cut v)
    lower a cut
    (OwnInputReference.readInput projected (FixedRows.rows plan) upper lower (LinearMap.ker A) a
      (OwnInputRawAssembly.scalarEval projected upper lower (FixedRows.repeats plan) cut) v)
    hgood hne
  exact hprediction.trans_eq
    (HierarchicalProjectedRawPrediction.conditional_prediction_eq slots projected projection
      (FixedRows.rows plan) upper lower lowerLevel original originalArrays lowerEvent
      (InitialParameters.useful δ) σ plan.density A (FixedRows.repeats plan) cut
      a externalLaw v hgood hne positive)

end
end PerfectCompleteness.HierarchicalProjectedRawMeeting

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalProjectedRawAverage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalProjectedRawAverage

noncomputable section

open scoped BigOperators Classical TensorProduct
open TreeSourceSpaces HierarchicalArrays UpperParameterScalars
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

private theorem event_mass_le_expectation {X : Type*} [Fintype X]
    (μ : FiniteDistribution X) (event : X → Bool) (value : X → ℝ) (factor : ℝ)
    (hnonneg : ∀ x, 0 ≤ value x)
    (hbound : ∀ x, event x = true → factor ≤ value x) :
    factor * μ.probability event ≤ μ.expectation value := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · rw [ite_eq_left hx]
    calc
      factor * μ.weight x = μ.weight x * factor := mul_comm _ _
      _ ≤ μ.weight x * value x :=
        mul_le_mul_of_nonneg_left (hbound x hx) (μ.nonnegative x)
  · rw [ite_eq_right hx, mul_zero]
    exact mul_nonneg (μ.nonnegative x) (hnonneg x)

variable {δ : ℚ} (plan : FixedRows.Plan δ) {branch : Nat → Nat} {t : Nat}
  (slots projected : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (projection : ∀ s j, MixedSupport.Projection (slots s j) (projected s j))
  (upper lower : Nodes branch plan.depth) (lowerLevel : Nat)
  {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (originalArrays : Ω → Arrays slots (FixedRows.rows plan))
  (lowerEvent : Ω → Bool)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) plan.order)
  (a : Block (FixedRows.rows plan) lower) (cut : OwnInputReference.Cut upper lower)

theorem factor_nonneg : 0 ≤ factor plan upper := by
  unfold factor
  positivity

theorem meeting_lower_of_goodRecord (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower))
    (v : Visible plan projected upper lower A cut)
    (hgood : goodRecord plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ
      A a cut externalLaw v = true) :
    factor plan upper ≤
      meetingProbability plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut v := by
  have hpositive := (PositiveFiberMass.goodRecord_iff
    (law plan projected upper lower A cut externalLaw)
    (fun sample : Raw plan projected upper lower A cut => sample.2)
    (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut)
    (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut)
    (rhoPred (InitialParameters.useful δ) plan.density) v).mp hgood
  let originalGiven : Raw plan projected upper lower A cut → Bool := fun sample =>
    J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
      @decide (sample.2 = v) (Classical.propDecidable _)
  have hgiven : originalGiven =
      HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan) upper lower lowerLevel
        original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
        (FixedRows.repeats plan) cut v := by
    funext sample
    unfold originalGiven HierarchicalProjectedRawPrediction.given
    apply congrArg (fun flag : Bool =>
      J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample && flag)
    exact (@decide_eq_decide _ _ _ _).mpr Iff.rfl
  have positive : 0 < (law plan projected upper lower A cut externalLaw).probability
      (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan) upper lower lowerLevel
        original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
        (FixedRows.repeats plan) cut v) := by
    rw [← hgiven]
    exact hpositive.1
  have conditional : rhoPred (InitialParameters.useful δ) plan.density ≤
      ((law plan projected upper lower A cut externalLaw).condition
        (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan) upper lower lowerLevel
          original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
          (FixedRows.repeats plan) cut v) positive).probability
        (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut) := by
    have hprediction := hpositive.2
    have hmatch : (fun sample : Raw plan projected upper lower A cut =>
        originalGiven sample &&
          prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample) =
        (fun sample =>
          (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
            prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample) &&
          @decide (sample.2 = v) (Classical.propDecidable _)) := by
      funext sample
      dsimp only [originalGiven]
      cases J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample <;>
        cases prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample <;>
        cases @decide (sample.2 = v) (Classical.propDecidable _) <;> rfl
    change rhoPred (InitialParameters.useful δ) plan.density ≤
      (law plan projected upper lower A cut externalLaw).probability
        (fun sample =>
          (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
            prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample) &&
          @decide (sample.2 = v) (Classical.propDecidable _)) /
      (law plan projected upper lower A cut externalLaw).probability originalGiven at hprediction
    rw [← hmatch, hgiven] at hprediction
    exact hprediction.trans_eq
      (FiniteDistribution.probability_condition (law plan projected upper lower A cut externalLaw)
        (HierarchicalProjectedRawPrediction.given slots projected projection (FixedRows.rows plan) upper lower lowerLevel
          original originalArrays lowerEvent (InitialParameters.useful δ) σ plan.density A
          (FixedRows.repeats plan) cut v)
        (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut)
        positive).symm
  exact HierarchicalProjectedRawMeeting.meeting_probability_lower plan slots projected projection upper lower lowerLevel
    original originalArrays lowerEvent σ A a cut v hδ externalLaw positive conditional

theorem expectedMeeting_ge_good_mass (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) :
    factor plan upper *
      (law plan projected upper lower A cut externalLaw).probability
        (goodEvent plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut externalLaw) ≤
      expectedMeeting plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut externalLaw := by
  apply event_mass_le_expectation
  · intro sample
    exact HierarchicalProjectedRawMeeting.meetingProbability_nonneg plan slots projected projection upper lower lowerLevel
      original originalArrays lowerEvent σ A a cut sample.2
  · intro sample hs
    exact meeting_lower_of_goodRecord plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ
      A a cut hδ externalLaw sample.2 (Bool.and_eq_true_iff.mp hs).2

theorem J_and_prediction :
    (fun sample => J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut sample &&
      prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut sample) =
      prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut := by
  funext sample
  unfold J prediction HierarchicalProjectedRawPrediction.rawJ HierarchicalProjectedRawPrediction.rawPrediction
    HierarchicalPrediction.prediction
  exact Bool.and_self_left _ _

theorem prediction_difference_le_good_mass (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) :
    (law plan projected upper lower A cut externalLaw).probability
        (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut) -
      rhoPred (InitialParameters.useful δ) plan.density *
        (law plan projected upper lower A cut externalLaw).probability
          (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut) ≤
      (law plan projected upper lower A cut externalLaw).probability
        (goodEvent plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut externalLaw) := by
  have h := PositiveFiberMass.difference_le_good_mass
    (law plan projected upper lower A cut externalLaw)
    (fun sample : Raw plan projected upper lower A cut => sample.2)
    (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut)
    (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut)
    (rhoPred (InitialParameters.useful δ) plan.density)
    (rhoPred_pos (InitialParameters.useful_pos hδ) plan.density_pos).le
  rw [J_and_prediction] at h
  exact h

theorem expectedMeeting_ge_prediction_difference_oai (hδ : 0 < δ)
    (externalLaw : FiniteDistribution
      (OwnInputReference.Exterior projected (FixedRows.rows plan) upper lower)) :
    factor plan upper *
      ((law plan projected upper lower A cut externalLaw).probability
          (prediction plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut) -
        rhoPred (InitialParameters.useful δ) plan.density *
          (law plan projected upper lower A cut externalLaw).probability
            (J plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A cut)) ≤
      expectedMeeting plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ A a cut externalLaw :=
  (mul_le_mul_of_nonneg_left
    (prediction_difference_le_good_mass plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ
      A a cut hδ externalLaw) (factor_nonneg plan upper)).trans
    (expectedMeeting_ge_good_mass plan slots projected projection upper lower lowerLevel original originalArrays lowerEvent σ
      A a cut hδ externalLaw)

end
end PerfectCompleteness.HierarchicalProjectedRawAverage

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.expectedMeeting_ge_prediction_difference_oai.{u_1} := @OAI.PerfectCompleteness.HierarchicalProjectedRawAverage.expectedMeeting_ge_prediction_difference_oai.{u_1}
