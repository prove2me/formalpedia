-- Prove2me | solution 1 for OAI.PerfectCompleteness.FixedLowerUniformCollision.supported_collision_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:22.564677+00:00
-- url     : https://prove2.me/submissions/8e1cdc35-0327-4241-bad6-ae5b730e6b90

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
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalLeftDecoder_adviceLaw_valid
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalLowerInverse_matrixTable_agreement_lt

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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

theorem expectation_product (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω × Γ → ℝ) :
    (μ.product ν).expectation f =
      μ.expectation (fun x => ν.expectation (fun y => f (x,y))) := by
  simp only [expectation, product, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_KernelSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace UniqueGamesTheorem.Foundations.Games

open scoped BigOperators
noncomputable section

namespace FiniteDistribution

/-- A full response table of nonzero weight uses a supported answer in every row. -/
theorem table_row_weight_ne_zero
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (answers : Q → A)
    (h : (table responses).weight answers ≠ 0) (q : Q) :
    (responses q).weight (answers q) ≠ 0 := by
  intro hq
  apply h
  change (∏ r, (responses r).weight (answers r)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ q) hq

end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_TwoResponseCollisionLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.DecoderTableAdmissibility

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

section FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem event_of_probability_one (μ : FiniteDistribution Ω) (event : Ω → Bool)
    (hone : μ.probability event = 1) (x : Ω) (hx : μ.weight x ≠ 0) :
    event x = true := by
  by_contra hfalse
  have hle (y : Ω) : (if event y then μ.weight y else 0) ≤ μ.weight y := by
    split
    · exact le_rfl
    · exact μ.nonnegative y
  have hlt : μ.probability event < ∑ y, μ.weight y := by
    unfold FiniteDistribution.probability
    apply Finset.sum_lt_sum (fun y _ => hle y)
    refine ⟨x, Finset.mem_univ _, ?_⟩
    simpa only [ite_eq_right hfalse] using
      lt_of_le_of_ne (μ.nonnegative x) (Ne.symm hx)
  have hbad : (1 : ℝ) < 1 := by simpa only [hone, μ.normalized] using hlt
  exact (lt_irrefl (1 : ℝ)) hbad

end FiniteLaw

end
end PerfectCompleteness.DecoderTableAdmissibility



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_AscendingBranchingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.DescendingRows

open scoped BigOperators Classical
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier
open UpperParameterScalars

noncomputable section

variable {κ α η : ℝ} (hκ : 0 < κ) (hα : 0 < α) (hη : 0 < η)

theorem cutoff_le_common (r depth : Nat) (rows : Nat → Nat) (i : Fin depth) :
    (lowerChoice hκ hα hη r (rows i.val)).cutoff ≤
      commonCutoff hκ hα hη r depth rows := by
  have hi : (lowerChoice hκ hα hη r (rows i.val)).cutoff ≤
      ∑ j : Fin depth, (lowerChoice hκ hα hη r (rows j.val)).cutoff :=
    Finset.single_le_sum
      (fun j _ => Nat.zero_le (lowerChoice hκ hα hη r (rows j.val)).cutoff)
      (Finset.mem_univ i)
  exact hi.trans (Nat.le_add_left _ _)

theorem tree_pair_requirement (r depth : Nat) (rows : Nat → Nat)
    (ordered : ∀ n, ∀ i : Fin n,
      (lowerChoice hκ hα hη r (rows i.val)).minimumRows ≤ rows n)
    {i j : Nat} (hij : i < j) (hj : j ≤ depth) :
    (lowerChoice hκ hα hη r (treeRows depth rows j)).minimumRows ≤
      treeRows depth rows i := by
  exact ordered (depth - i) ⟨depth - j, by omega⟩

theorem tree_cutoff_le_common (r depth : Nat) (rows : Nat → Nat)
    {j : Nat} (hj : 0 < j) (hjd : j ≤ depth) :
    (lowerChoice hκ hα hη r (treeRows depth rows j)).cutoff ≤
      commonCutoff hκ hα hη r depth rows :=
  cutoff_le_common hκ hα hη r depth rows ⟨depth - j, by omega⟩

end
end PerfectCompleteness.DescendingRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteRangeInverse
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteRangeInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)
open PerfectCompleteness.PartialTableInverse

attribute [local instance] linearMapFintype

universe u v w

variable {H : Type u} {K : Type v} {Y : Type w}
  [AddCommGroup H] [Module F2 H] [AddCommGroup K] [Module F2 K]
  [Fintype H] [Fintype K] [Fintype Y]
  [FiniteDimensional F2 H] [FiniteDimensional F2 K]

omit [Fintype Y] [FiniteDimensional F2 K] in
theorem agreement_eq_nonzeroAgreement
    (f : (Module.Dual F2 H →ₗ[F2] K) → Option Y) :
    agreement f = nonzeroAgreement f := by
  apply Finset.expect_congr rfl
  intro a _
  apply Finset.expect_congr rfl
  intro X _
  exact Fintype.expect_equiv (Module.evalEquiv F2 H).toEquiv
    (fun h : H => definedEquality f X (matrixStep X a.val h))
    (fun φ : Module.Dual F2 (Module.Dual F2 H) =>
      definedEquality f X (X + φ.smulRight a.val)) (fun _ => rfl)

end
end PerfectCompleteness.FiniteRangeInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_BucketQuotientAgreement
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.DecoderTableCoupling.definedEqual_collision _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BucketQuotientAgreement

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)
open PartialTableInverse (definedEquality nonzeroAgreement)

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

theorem probability_collision_eq_expectation {A B Y : Type*}
    [Fintype A] [Fintype B] [Fintype Y]
    (μ : FiniteDistribution A) (f : B → Option Y) (p q : A → B) :
    μ.probability (fun x => TwoResponseCollision.collision f (p x, q x)) =
      μ.expectation (fun x => definedEquality f (p x) (q x)) := by
  unfold FiniteDistribution.probability FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : ∃ y, f (p x) = some y ∧ f (q x) = some y <;>
    simp [TwoResponseCollision.collision, definedEquality, h]

end
end PerfectCompleteness.BucketQuotientAgreement

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalDecoderTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

variable (hbranch : ∀ k < n, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

local instance rowSpaceFintype_r2bb341_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.RowSpace slots node) := Fintype.ofFinite _
local instance nodeSpaceFintype_r2bb341_1 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
local instance upperDualFintype_r2bb341_1 :
    Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper)) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
local instance adviceFintype_r2bb341_1 (r : Nat) :
    Fintype (Advice slots upper lowerLevel background r) := by
  letI : Fintype (Module.Dual F2 (NodeEmbedding.RowSpace slots upper ⧸
      HierarchicalFrozenTables.knownRows slots upper lowerLevel background)) :=
    LeftDecoder.dualFintype
  infer_instance
local instance answerFintype_r2bb341_1 (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (Answer slots upper lowerLevel d) :=
  LeftDecoder.dualFintype (V := squareSpace (LowerH slots upper lowerLevel d))
theorem decode_valid
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat)
    (q : Module.Dual F2 (NodeEmbedding.RowSpace slots upper))
    (hq : HierarchicalLeftDecoder.Valid slots upper lowerLevel hbranch background q)
    (z : Answer slots upper lowerLevel d)
    (hz : decode slots upper lowerLevel hbranch d s q = some z) :
    Valid slots upper lowerLevel background hbranch d s z := by
  change (if fullRank slots upper lowerLevel d
      (HierarchicalLeftDecoder.output slots upper lowerLevel hbranch d q) ≤ s then none
    else some (HierarchicalLeftDecoder.output slots upper lowerLevel hbranch d q)) = some z at hz
  split at hz
  · cases hz
  · rename_i hrank
    have heq := Option.some.inj hz
    subst z
    exact ⟨(hq d).1, (hq d).2, Nat.lt_of_not_ge hrank⟩

end
end PerfectCompleteness.HierarchicalDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalAllDecoderTables
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalAllDecoderTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays PointwiseSpaces
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

variable (hbranch : ∀ k < n, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (background : Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background → Prop)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAllDecoderTables.rowSpaceFintype
local instance nodeSpaceFintype_r2bb341_2 (node : Nodes branch n) :
    Fintype (NodeEmbedding.NodeH slots node) := Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAllDecoderTables.upperDualFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAllDecoderTables.answerFintype
theorem supported_upper_table_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (table : Input (rows := rows) slots upper lowerLevel r → UpperAnswer slots upper)
    (hsupport : (upperTableLaw slots upper lowerLevel σ useful r ρ).weight table ≠ 0)
    (input : Input (rows := rows) slots upper lowerLevel r) :
    HierarchicalLeftDecoder.Valid slots upper lowerLevel hbranch input.1 (table input) := by
  have hrow := FiniteDistribution.table_row_weight_ne_zero
    (upperKernel slots upper lowerLevel σ useful r ρ) table hsupport input
  exact of_decide_eq_true (DecoderTableAdmissibility.event_of_probability_one
    (upperKernel slots upper lowerLevel σ useful r ρ input)
    (fun q => decide (HierarchicalLeftDecoder.Valid slots upper lowerLevel hbranch input.1 q))
    (HierarchicalLeftDecoder.adviceLaw_valid slots upper lowerLevel hbranch input.1
      σ (useful input.1) r ρ hρ input.2.1 input.2.2) (table input) hrow)

theorem decoded_supported_table_valid (r : Nat) (ρ : ℝ) (hρ : 0 < ρ)
    (table : Input (rows := rows) slots upper lowerLevel r → UpperAnswer slots upper)
    (hsupport : (upperTableLaw slots upper lowerLevel σ useful r ρ).weight table ≠ 0)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) (s : Nat) :
    DecoderTableAdmissibility.Admissible (RowValid slots upper lowerLevel hbranch r d s)
      (decodeTable slots upper lowerLevel hbranch r d s table) := by
  intro input z hz
  exact HierarchicalDecoderTables.decode_valid slots upper lowerLevel input.1 hbranch d s
    (table input) (supported_upper_table_valid slots upper lowerLevel hbranch σ useful
      r ρ hρ table hsupport input) z hz

end
end PerfectCompleteness.HierarchicalAllDecoderTables

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Reduction_FixedRows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedRows

open InitialParameters UpperParameterScalars
open UniqueGamesTheorem.Appendix UniqueGamesTheorem.Fourier

noncomputable section

variable {δ : ℚ} (plan : Plan δ)

theorem lower_row_requirement (hδ : 0 < δ) {i j : Nat}
    (hij : i < j) (hj : j ≤ plan.depth) :
    (DescendingRows.lowerChoice (useful_pos hδ) plan.density_pos (inverse_pos hδ)
      plan.order (rows plan j)).minimumRows ≤ rows plan i :=
  DescendingRows.tree_pair_requirement (useful_pos hδ) plan.density_pos (inverse_pos hδ)
    plan.order plan.depth plan.rootFirstRows (plan.lowerRequirements hδ) hij hj

end
end PerfectCompleteness.FixedRows

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalLowerInverseLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalLowerInverse

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

variable (hbranch : ∀ k < n, 0 < branch k)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel bg → Prop)

include hbranch σ useful

local instance lowerHFintype_r2bb341_1 (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.HierarchicalLowerInverse.answerFintype
local instance upperDualFintype_r2bb341_2 : Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper
theorem supported_upper_matrixTable_agreement_lt {r s m adviceRows : Nat}
    (decoderDensity : ℝ) (hdecoderDensity : 0 < decoderDensity)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel adviceRows →
      HierarchicalAllDecoderTables.UpperAnswer slots upper)
    (hsupport : (HierarchicalAllDecoderTables.upperTableLaw slots upper lowerLevel σ useful
      adviceRows decoderDensity).weight table ≠ 0)
    (ρ η : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    PartialTableInverse.nonzeroAgreement
      (matrixTable slots upper lowerLevel background d upperMatrix A
        (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d s table)) < η := by
  exact matrixTable_agreement_lt slots upper lowerLevel background hbranch
    d upperMatrix A
    (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d s table)
    (HierarchicalAllDecoderTables.decoded_supported_table_valid slots upper lowerLevel hbranch
      σ useful adviceRows decoderDensity hdecoderDensity table hsupport d s)
    ρ η hm hρ hρ1 hconstants hrows herror

end
end PerfectCompleteness.HierarchicalLowerInverse

end

section

namespace PerfectCompleteness.HierarchicalFixedLowerInverse

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

variable {δ : ℚ} (plan : FixedRows.Plan δ) (hδ : 0 < δ)
  {branch : Nat → Nat} {t : Nat}
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background
    (rows := FixedRows.rows plan) slots upper)

variable (hbranch : ∀ k < plan.depth, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (useful : (bg : HierarchicalMatrixTable.Background
      (rows := FixedRows.rows plan) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel bg → Prop)

include hbranch σ useful

local instance lowerHFintype_r2bb341_2 (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _
local instance upperDualFintype_r2bb341_3 : Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper
theorem supported_upper_matrixTable_agreement_lt {adviceRows : Nat}
    (decoderDensity : ℝ) (hdecoderDensity : 0 < decoderDensity)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix
      (rows := FixedRows.rows plan) slots upper)
    (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input
      (rows := FixedRows.rows plan) slots upper lowerLevel adviceRows →
        HierarchicalAllDecoderTables.UpperAnswer slots upper)
    (hsupport : (HierarchicalAllDecoderTables.upperTableLaw slots upper lowerLevel σ useful
      adviceRows decoderDensity).weight table ≠ 0) :
    PartialTableInverse.nonzeroAgreement
      (HierarchicalLowerInverse.matrixTable slots upper lowerLevel background d upperMatrix A
        (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d
          (FixedRows.cutoff plan hδ) table)) <
      UpperParameterScalars.gamma (InitialParameters.useful δ) plan.density
        (InitialParameters.inverse δ) plan.order
        (FixedRows.rows plan (Nodes.height upper)) ^ 2 / 8 := by
  let lower := DescendingRows.lowerChoice (InitialParameters.useful_pos hδ)
    plan.density_pos (InitialParameters.inverse_pos hδ) plan.order
    (FixedRows.rows plan (Nodes.height upper))
  have hheight : Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d) =
      lowerLevel :=
    (RelativeDescendantProducts.relativeNode_height upper d.val.val).trans d.property
  have hproper : lowerLevel < Nodes.height upper := by
    rw [← hheight]
    exact (RelativeDescendantProducts.descendantIndex_below upper d.val).height_lt
  have hminimum : lower.minimumRows ≤ FixedRows.rows plan lowerLevel :=
    FixedRows.lower_row_requirement plan hδ hproper (Nodes.height_le upper)
  have hrows : 2 * lower.crossSize + lower.order ≤
      FixedRows.rows plan (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)) := by
    rw [hheight]
    exact lower.row_bound _ hminimum
  have hcutoff : lower.cutoff ≤ FixedRows.cutoff plan hδ := by
    simpa only [lower, FixedRows.rows, FixedRows.cutoff] using
      DescendingRows.tree_cutoff_le_common (InitialParameters.useful_pos hδ)
        plan.density_pos (InitialParameters.inverse_pos hδ) plan.order plan.depth
        plan.rootFirstRows (Nat.zero_lt_of_lt hproper) (Nodes.height_le upper)
  exact HierarchicalLowerInverse.supported_upper_matrixTable_agreement_lt
    (r := lower.order) (s := FixedRows.cutoff plan hδ) (m := lower.crossSize)
    slots upper lowerLevel background hbranch σ useful decoderDensity hdecoderDensity
    d upperMatrix A table hsupport lower.density _ lower.cross_pos lower.density_pos
    lower.density_lt_one lower.spectral hrows (lower.error_bound _ hcutoff).le

end
end PerfectCompleteness.HierarchicalFixedLowerInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_FixedLowerUniformCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FixedLowerUniformCollision

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] UniqueGamesTheorem.Appendix.RankLevelFilter.linearMapFintype

private theorem expectation_uniform_eq_expect {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    (FiniteDistribution.uniform A).expectation f = 𝔼 x : A, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

section Uniform

variable {Ω Y : Type*} [Fintype Y]
  (V : Submodule F2 (Ω → F2)) [Fintype V] [FiniteDimensional F2 V]
  (ℓ : Nat) [Nonempty (BucketSampler.Direction ℓ)]

theorem uniform_collision_eq (f : BucketMatrixResampling.Matrix V ℓ → Option Y) :
    (uniformLaw V ℓ).probability (uniformCollision V ℓ f) =
      PartialTableInverse.nonzeroAgreement f := by
  unfold uniformLaw uniformCollision
  rw [BucketQuotientAgreement.probability_collision_eq_expectation]
  simp only [FiniteDistribution.expectation_product, expectation_uniform_eq_expect]
  calc
    _ = FiniteRangeInverse.agreement f := by
      unfold FiniteRangeInverse.agreement
      refine Finset.expect_congr (ι := BucketSampler.Direction ℓ) ?_ ?_
      · ext a
        simp only [Finset.mem_univ]
      intro a _
      rfl
    _ = _ := FiniteRangeInverse.agreement_eq_nonzeroAgreement f

end Uniform

variable {δ : ℚ} (plan : FixedRows.Plan δ) (hδ : 0 < δ)
  {branch : Nat → Nat} {t : Nat}
  (slots : RecursiveSpaces.Slots branch plan.depth → Fin t → MixedSupport.Slot)
  (upper : Nodes branch plan.depth) (lowerLevel : Nat)
  (background : HierarchicalMatrixTable.Background (rows := FixedRows.rows plan) slots upper)

variable (hbranch : ∀ k < plan.depth, 0 < branch k)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch plan.depth t))
  (useful : (bg : HierarchicalMatrixTable.Background
      (rows := FixedRows.rows plan) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel bg → Prop)

include hbranch σ useful

attribute [local instance] OAI.PerfectCompleteness.FixedLowerUniformCollision.lowerHFintype
local instance upperDualFintype_r2bb341_4 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper
attribute [local instance] OAI.PerfectCompleteness.FixedLowerUniformCollision.directionNonempty
theorem supported_collision_lt_oai {adviceRows : Nat}
    (density : ℝ) (hdensity : 0 < density)
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := FixedRows.rows plan) slots upper)
    (A : ManyGoodRows.RowMap (Block (FixedRows.rows plan) upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input
      (rows := FixedRows.rows plan) slots upper lowerLevel adviceRows →
        HierarchicalAllDecoderTables.UpperAnswer slots upper)
    (hsupport : (HierarchicalAllDecoderTables.upperTableLaw slots upper lowerLevel σ useful
      adviceRows density).weight table ≠ 0) :
    (uniformLaw (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
      (FixedRows.rows plan (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))).probability
        (uniformCollision _ _
        (HierarchicalLowerInverse.matrixTable slots upper lowerLevel background d upperMatrix A
          (HierarchicalAllDecoderTables.decodeTable slots upper lowerLevel hbranch adviceRows d
            (FixedRows.cutoff plan hδ) table))) <
      UpperParameterScalars.gamma (InitialParameters.useful δ) plan.density
        (InitialParameters.inverse δ) plan.order
        (FixedRows.rows plan (Nodes.height upper)) ^ 2 / 8 := by
  rw [uniform_collision_eq]
  exact HierarchicalFixedLowerInverse.supported_upper_matrixTable_agreement_lt
    plan hδ slots upper lowerLevel background hbranch σ useful density hdensity
    d upperMatrix A table hsupport

end
end PerfectCompleteness.FixedLowerUniformCollision

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.FixedLowerUniformCollision.supported_collision_lt_oai := @OAI.PerfectCompleteness.FixedLowerUniformCollision.supported_collision_lt_oai
