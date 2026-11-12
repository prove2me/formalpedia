-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalLowerInverse.matrixTable_agreement_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:23.72994+00:00
-- url     : https://prove2.me/submissions/0f40df88-e57c-4480-8d0d-33ee97efc187

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
import Theorems.Thm_OAI_PerfectCompleteness_LowerAffineSliceRank_slice_probability_le_of_coordinates
import Theorems.Thm_OAI_PerfectCompleteness_MatrixInverse_noiseEnergy_le_of_global

section
-- module Solutions.OAIQ252_PC.UniqueGames_Analysis_A13IndexLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Appendix.Derivatives.hybridIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
The real-valued finite-probability steps at the end of Appendix A.5.

The results here prove normalized Cauchy--Schwarz/Hölder consequences and
Boolean moment identities. They do not introduce Proposition A.5 or Lemma A.6
as axioms, and do not identify a conditional estimate with Theorem 2.3.
-/

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem boolean_positive_moment {f : α → ℝ} (hf : IsBoolean f)
    (k : ℕ) (hk : 0 < k) : (𝔼 x, f x ^ k) = 𝔼 x, f x := by
  apply Finset.expect_congr rfl
  intro x _
  rcases hf x with h | h <;> simp [h, Nat.ne_of_gt hk]

theorem boolean_squared_norm_eq_density {f : α → ℝ} (hf : IsBoolean f) :
    (𝔼 x, f x ^ 2) = 𝔼 x, f x :=
  boolean_positive_moment hf 2 (by decide)

end UniqueGamesTheorem.Appendix.LevelInequality

noncomputable section

namespace UniqueGamesTheorem.Appendix.LevelInequality

open scoped BigOperators
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier

section ActualLinearMaps

variable {E F : Type*}
variable [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
variable [FiniteDimensional F2 E] [FiniteDimensional F2 F]
variable [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

variable [Finite E] [Finite F]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] [Finite E] [Finite F] in
theorem boolean_restriction (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F) :
    IsBoolean (UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T) := by
  intro N
  exact hf (UniqueGamesTheorem.Fourier.MatrixRestrictions.translate A B T N)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
/-- On Boolean functions the restriction-global norm bound is exactly the
restriction-density hypothesis in Theorem 2.3. -/
theorem boolean_global_iff_density (f : (E →ₗ[F2] F) → ℝ) (hf : IsBoolean f)
    (d : ℕ) (η : ℝ) :
    IsRestrictionGlobal f d η ↔
      ∀ (A : Submodule F2 E) (B : Submodule F2 F) (T : E →ₗ[F2] F),
        UniqueGamesTheorem.Fourier.MatrixRestrictions.order A B ≤ d →
          (𝔼 N, UniqueGamesTheorem.Fourier.MatrixRestrictions.restrict f A B T N) ≤ η := by
  unfold IsRestrictionGlobal
  simp_rw [boolean_squared_norm_eq_density (boolean_restriction f hf _ _ _)]

end ActualLinearMaps

end UniqueGamesTheorem.Appendix.LevelInequality

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GlobalityLemmas
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section

namespace UniqueGamesTheorem.Fourier.MatrixLevelBridge

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Appendix.LevelInequality

theorem levelCutoffConstant_nonneg (r : Nat) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    0 ≤ levelCutoffConstant r ρ := by
  unfold levelCutoffConstant
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact hρ
  · exact mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
      (Real.rpow_nonneg hρ _)

end UniqueGamesTheorem.Fourier.MatrixLevelBridge

end

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixInverse
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixFourier
open UniqueGamesTheorem.Fourier.MatrixNoise UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

theorem exists_dense_restriction_of_family {Y : Type*} [Fintype Y]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : Y → (E →ₗ[F2] F) → ℝ) (hf : ∀ y, IsBoolean (f y))
    (hmass : (∑ y, 𝔼 X, f y X ^ 2) ≤ 1)
    (hretention : η ≤ ∑ y, noiseEnergy (f y)) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (f y) W C' T N) := by
  by_contra hnone
  have hg (y : Y) : IsRestrictionGlobal (f y) r ρ := by
    apply (boolean_global_iff_density (f y) (hf y) r ρ).mpr
    intro W C' T horder
    apply le_of_not_gt
    intro hdense
    exact hnone ⟨y, W, C', T, horder, hdense⟩
  have hbound : (∑ y, noiseEnergy (f y)) ≤
      (levelCutoffConstant r ρ + node (r + 1)) * (∑ y, 𝔼 X, f y X ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun y _ => noiseEnergy_le_of_global r ρ hρ hρ1 (f y) (hf y) (hg y)
  have hnonneg : 0 ≤ levelCutoffConstant r ρ + node (r + 1) :=
    add_nonneg (levelCutoffConstant_nonneg r ρ hρ.le) (node_pos _).le
  have hbound' := hbound.trans (mul_le_mul_of_nonneg_left hmass hnonneg)
  simp only [mul_one] at hbound'
  exact (not_lt_of_ge (hretention.trans hbound')) hconstants

end
end PerfectCompleteness.MatrixInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DummyEliminationLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.NonzeroAverage

open scoped BigOperators

variable {A : Type*} [Fintype A] [DecidableEq A]

theorem card_subtype_ne_real (a : A) :
    (Fintype.card {x : A // x ≠ a} : ℝ) = (Fintype.card A : ℝ) - 1 := by
  have h : (Fintype.card A : ℝ) =
      1 + (Fintype.card {x : A // x ≠ a} : ℝ) := by
    simpa using Fintype.sum_eq_add_sum_subtype_ne (fun _ : A => (1 : ℝ)) a
  linarith

theorem card_mul_expect_eq (g : A → ℝ) (a : A) :
    (Fintype.card A : ℝ) * (𝔼 x, g x) =
      g a + (Fintype.card {x : A // x ≠ a} : ℝ) *
        (𝔼 x : {x : A // x ≠ a}, g x.1) := by
  rw [Fintype.card_mul_expect, Fintype.card_mul_expect]
  exact Fintype.sum_eq_add_sum_subtype_ne g a

theorem card_mul_expect_eq_sub_one (g : A → ℝ) (a : A) :
    (Fintype.card A : ℝ) * (𝔼 x, g x) =
      g a + ((Fintype.card A : ℝ) - 1) *
        (𝔼 x : {x : A // x ≠ a}, g x.1) := by
  rw [← card_subtype_ne_real a]
  exact card_mul_expect_eq g a

theorem expect_subtype_ne_le_expect_of_expect_le (g : A → ℝ) (a : A)
    (h : (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ g a) :
    (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ (𝔼 x, g x) := by
  let : Nonempty A := ⟨a⟩
  have hcard : 0 < (Fintype.card A : ℝ) := by
    exact_mod_cast Fintype.card_pos
  apply (mul_le_mul_iff_right₀ hcard).mp
  have hid := card_mul_expect_eq_sub_one g a
  nlinarith

theorem expect_subtype_ne_le_expect [Nontrivial A] (g : A → ℝ) (a : A)
    (h : ∀ x, g x ≤ g a) :
    (𝔼 x : {x : A // x ≠ a}, g x.1) ≤ (𝔼 x, g x) := by
  obtain ⟨b, hb⟩ := exists_ne a
  let : Nonempty {x : A // x ≠ a} := ⟨⟨b, hb⟩⟩
  apply expect_subtype_ne_le_expect_of_expect_le g a
  exact Finset.expect_le Finset.univ_nonempty (fun x _ => h x.1)

theorem nonzero_expect_le_expect [Zero A] [Nontrivial A] (g : A → ℝ)
    (h : ∀ x, g x ≤ g 0) :
    (𝔼 x : {x : A // x ≠ (0 : A)}, g x.1) ≤ (𝔼 x, g x) :=
  expect_subtype_ne_le_expect g 0 h

end PerfectCompleteness.NonzeroAverage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_PartialTableInverse
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceFintype _root_.OAI.PerfectCompleteness.MatrixSlice.sliceNonempty _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesFintype _root_.OAI.PerfectCompleteness.PulledColumnSpace.candidatesNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instFinitePart _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.PoweringLabels.finitePortWords
attribute [-simp] _root_.OAI.PerfectCompleteness.FiniteRangeInverse.matrixStep_apply _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.PartialTableInverse

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters UniqueGamesTheorem.Fourier.MatrixNoise
open UniqueGamesTheorem.Fourier.MatrixRestrictions UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.LevelInequality UniqueGamesTheorem.Appendix.RankLevelFilter
open PerfectCompleteness.MatrixInverse

variable {Ω Y : Type*} [Fintype Y]

omit [Fintype Y] in
theorem indicator_boolean (f : Ω → Option Y) (y : Y) : IsBoolean (indicator f y) := by
  intro X
  unfold indicator
  split_ifs <;> simp

theorem sum_indicator_sq_le (f : Ω → Option Y) (X : Ω) :
    (∑ y, indicator f y X ^ 2) ≤ 1 := by
  cases h : f X <;> simp [indicator, h, eq_comm]

theorem definedEquality_eq_sum (f : Ω → Option Y) (X X' : Ω) :
    definedEquality f X X' = ∑ y, indicator f y X * indicator f y X' := by
  cases h : f X <;> cases h' : f X' <;>
    simp [definedEquality, indicator, h, h', mul_ite, eq_comm]

omit [Fintype Y] in
theorem definedEquality_le_self (f : Ω → Option Y) (X X' : Ω) :
    definedEquality f X X' ≤ definedEquality f X X := by
  unfold definedEquality
  split_ifs with h h' h'
  · exact le_rfl
  · obtain ⟨y, hy, _⟩ := h
    exact (h' ⟨y, hy, hy⟩).elim
  · norm_num
  · exact le_rfl

variable {E F : Type*}
  [AddCommGroup E] [Module F2 E] [AddCommGroup F] [Module F2 F]
  [FiniteDimensional F2 E] [FiniteDimensional F2 F]
  [Finite E] [Fintype F] [Fintype (E →ₗ[F2] F2)]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (E →ₗ[F2] F)] [Fintype (F →ₗ[F2] E)] in
theorem uniform_operator_eq_average (g : (E →ₗ[F2] F) → ℝ) (X : E →ₗ[F2] F) :
    linearRealNoiseOperator (fun _ : F => (Fintype.card F : ℝ)⁻¹) g X =
      𝔼 a : F, 𝔼 h : E →ₗ[F2] F2, g (X + h.smulRight a) := by
  unfold linearRealNoiseOperator
  simp only [Fintype.expect_eq_sum_div_card, div_eq_mul_inv]
  rw [← Finset.mul_sum]
  exact mul_comm _ _

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] in
theorem noiseEnergy_eq_average (g : (E →ₗ[F2] F) → ℝ) :
    noiseEnergy g =
      𝔼 X, 𝔼 a : F, 𝔼 h : E →ₗ[F2] F2, g X * g (X + h.smulRight a) := by
  unfold noiseEnergy
  simp_rw [uniform_operator_eq_average, Finset.mul_expect]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] in
theorem allAgreement_eq_sum (f : (E →ₗ[F2] F) → Option Y) :
    allAgreement f = ∑ y, noiseEnergy (indicator f y) := by
  unfold allAgreement stepAgreement
  rw [Finset.expect_comm]
  simp_rw [definedEquality_eq_sum, Finset.expect_sum_comm, ← noiseEnergy_eq_average]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype F] [Fintype (E →ₗ[F2] F2)] [Fintype (F →ₗ[F2] E)] in
theorem indicator_mass_le_one (f : (E →ₗ[F2] F) → Option Y) :
    (∑ y, 𝔼 X, indicator f y X ^ 2) ≤ 1 := by
  rw [← Finset.expect_sum_comm]
  calc
    _ ≤ 𝔼 _X : E →ₗ[F2] F, (1 : ℝ) :=
      Finset.expect_le_expect fun X _ => sum_indicator_sq_le f X
    _ = 1 := Fintype.expect_const _

theorem exists_dense_slice_all (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ allAgreement f) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (indicator f y) W C' T N) := by
  apply exists_dense_restriction_of_family r ρ η hρ hρ1 hconstants (indicator f)
    (indicator_boolean f) (indicator_mass_le_one f)
  rwa [← allAgreement_eq_sum]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype F] [Fintype (F →ₗ[F2] E)] [Fintype Y] in
theorem stepAgreement_le_zero (f : (E →ₗ[F2] F) → Option Y) (a : F) :
    stepAgreement f a ≤ stepAgreement f 0 := by
  apply Finset.expect_le_expect
  intro X _
  apply Finset.expect_le_expect
  intro h _
  simpa using definedEquality_le_self f X (X + h.smulRight a)

omit [FiniteDimensional F2 E] [FiniteDimensional F2 F] [Finite E]
  [Fintype (F →ₗ[F2] E)] [Fintype Y] in
theorem nonzeroAgreement_le_all [Nontrivial F]
    (f : (E →ₗ[F2] F) → Option Y) :
    nonzeroAgreement f ≤ allAgreement f :=
  PerfectCompleteness.NonzeroAverage.nonzero_expect_le_expect
    (stepAgreement f) (stepAgreement_le_zero f)

theorem exists_dense_slice_nonzero [Nontrivial F]
    (r : Nat) (ρ η : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (f : (E →ₗ[F2] F) → Option Y) (hagreement : η ≤ nonzeroAgreement f) :
    ∃ (y : Y) (W : Submodule F2 E) (C' : Submodule F2 F) (T : E →ₗ[F2] F),
      order W C' ≤ r ∧ ρ < (𝔼 N, restrict (indicator f y) W C' T N) :=
  exists_dense_slice_all r ρ η hρ hρ1 hconstants f
    (hagreement.trans (nonzeroAgreement_le_all f))

end
end PerfectCompleteness.PartialTableInverse

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixErasure
attribute [-simp] _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.MatrixErasure

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Fourier.MatrixCharacters
open PerfectCompleteness.PartialTableInverse

variable {Ω Y : Type*}

theorem erase_eq_of_not (f : Ω → Option Y) (T : Ω → Prop)
    {X : Ω} (hX : ¬T X) : erase f T X = f X := by
  simp [erase, hX]

theorem erase_eq_some_iff (f : Ω → Option Y) (T : Ω → Prop) (X : Ω) (y : Y) :
    erase f T X = some y ↔ ¬T X ∧ f X = some y := by
  by_cases hX : T X <;> simp [erase, hX]

end
end PerfectCompleteness.MatrixErasure

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_LowerAffineSliceRank
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawFintype _root_.OAI.PerfectCompleteness.CleanTreeFactors.rawNonempty _root_.OAI.PerfectCompleteness.CutChildCleanLaw.rawFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OwnInputReference.rawSampleFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.LowerAffineSliceRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open BilinearGramCompression

variable {E : Type*} [AddCommGroup E] [Module F2 E]
  [Fintype E] [FiniteDimensional F2 E]
  {ℓ m : Nat}
  [Fintype (Module.Dual F2 E)]

theorem slice_rank_probability_le_of_rank_gt
    (W : Submodule F2 E) (C' : Submodule F2 (Fin ℓ → F2))
    (X : E →ₗ[F2] (Fin ℓ → F2))
    (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))
    (r s : Nat) (horder : order W C' ≤ r) (hrows : 2 * m + r ≤ ℓ)
    (hrank : s < Module.finrank F2 (LinearMap.range F)) :
    (FiniteDistribution.uniform (Parameter W C')).probability
        (fun A => decide ((testedGram F (translate W C' X A)).rank ≤ 1)) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
        (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  let b := Module.finBasis F2 C'
  have hW : Module.finrank F2 W ≤ r := (Nat.le_add_right _ _).trans horder
  have hdim : 2 * m ≤ Module.finrank F2 C' := by
    have htotal := C'.finrank_quotient_add_finrank
    have hfull : Module.finrank F2 (Fin ℓ → F2) = ℓ := by
      simp [Module.finrank_fintype_fun_eq_card]
    rw [hfull] at htotal
    unfold order at horder
    omega
  obtain ⟨sel⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin m ⊕ Fin m) ≤
      Fintype.card (Fin (Module.finrank F2 C')) by
      simpa only [Fintype.card_sum, Fintype.card_fin, two_mul] using hdim)
  let coordinates : Fin (Module.finrank F2 C') → Module.Dual F2 (Fin ℓ → F2) :=
    fun i => Subspace.dualLift C' (b.coord i)
  have hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i := by
    intro i
    apply LinearMap.ext
    intro x
    change Subspace.dualLift C' (b.coord i) (x : Fin ℓ → F2) = b.coord i x
    exact Subspace.dualLift_of_subtype (φ := b.coord i) x
  exact slice_probability_le_of_coordinates W C' b sel sel.injective
    coordinates hcoordinates X F r s hW hrank


variable {Y : Type*} [Fintype Y]
  (f : (E →ₗ[F2] (Fin ℓ → F2)) → Option Y)
  (form : Y → Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))

private theorem probability_eq_expect_indicator {A : Type*} [Fintype A] [Nonempty A]
    (event : A → Bool) :
    (FiniteDistribution.uniform A).probability event =
      𝔼 a : A, if event a then (1 : ℝ) else 0 := by
  have h : (FiniteDistribution.uniform A).probability event =
      (FiniteDistribution.uniform A).expectation (fun a => if event a then (1 : ℝ) else 0) := by
    simp [FiniteDistribution.probability, FiniteDistribution.expectation, mul_ite]
  rw [h, FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

omit [Fintype Y] in
theorem dense_value_rank_le
    (tested : ∀ X y, f X = some y → (testedGram (form y) X).rank ≤ 1)
    (W : Submodule F2 E) (C' : Submodule F2 (Fin ℓ → F2))
    (X : E →ₗ[F2] (Fin ℓ → F2)) (y : Y)
    (r s : Nat) (ρ : ℝ) (horder : order W C' ≤ r) (hrows : 2 * m + r ≤ ℓ)
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ)
    (hdense : ρ < 𝔼 A : Parameter W C',
      restrict (PartialTableInverse.indicator f y) W C' X A) :
    Module.finrank F2 (LinearMap.range (form y)) ≤ s := by
  by_contra h
  have hbound := slice_rank_probability_le_of_rank_gt W C' X (form y) r s
    horder hrows (Nat.lt_of_not_ge h)
  have hdom : (𝔼 A : Parameter W C',
      restrict (PartialTableInverse.indicator f y) W C' X A) ≤
      (FiniteDistribution.uniform (Parameter W C')).probability
        (fun A => decide ((testedGram (form y) (translate W C' X A)).rank ≤ 1)) := by
    rw [probability_eq_expect_indicator]
    apply Finset.expect_le_expect
    intro A _
    by_cases hf : f (translate W C' X A) = some y
    · simp [restrict, PartialTableInverse.indicator, hf, tested _ _ hf]
    · simp only [restrict, PartialTableInverse.indicator, ite_eq_right hf]
      split_ifs <;> norm_num
  exact (not_le_of_gt hdense) (hdom.trans (hbound.trans herror))

theorem high_rank_agreement_lt
    [Fintype (E →ₗ[F2] (Fin ℓ → F2))]
    [Fintype ((Fin ℓ → F2) →ₗ[F2] E)]
    (tested : ∀ X y, f X = some y → (testedGram (form y) X).rank ≤ 1)
    (r s : Nat) (ρ η : ℝ) (hm : 0 < m)
    (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ ℓ)
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    PartialTableInverse.nonzeroAgreement
      (MatrixErasure.erase f (fun X => ∃ y, f X = some y ∧
        Module.finrank F2 (LinearMap.range (form y)) ≤ s)) < η := by
  have hℓ : 0 < ℓ := by omega
  let : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  let T := fun X => ∃ y, f X = some y ∧
    Module.finrank F2 (LinearMap.range (form y)) ≤ s
  let g := MatrixErasure.erase f T
  have htested : ∀ X y, g X = some y → (testedGram (form y) X).rank ≤ 1 := by
    intro X y h
    exact tested X y ((MatrixErasure.erase_eq_some_iff f T X y).mp h).2
  by_contra h
  have hagreement : η ≤ PartialTableInverse.nonzeroAgreement g := le_of_not_gt h
  obtain ⟨y, W, C', X, horder, hdense⟩ :=
    PartialTableInverse.exists_dense_slice_nonzero r ρ η hρ hρ1 hconstants g hagreement
  have hrank := dense_value_rank_le g form htested W C' X y r s ρ horder hrows herror hdense
  have hnone (A : Parameter W C') : g (translate W C' X A) ≠ some y := by
    intro h
    have he := (MatrixErasure.erase_eq_some_iff f T _ y).mp h
    exact he.1 ⟨y, he.2, hrank⟩
  have hzero : (𝔼 A : Parameter W C',
      restrict (PartialTableInverse.indicator g y) W C' X A) = 0 := by
    apply Finset.expect_eq_zero
    intro A _
    simp [restrict, PartialTableInverse.indicator, hnone A]
  rw [hzero] at hdense
  exact (not_lt_of_ge hρ.le) hdense


end
end PerfectCompleteness.LowerAffineSliceRank

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_FunctionSpaceLowerRank
attribute [-simp] _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FunctionSpaceLowerRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter
open PointwiseSpaces

section Transport

variable {K H V : Type*} [Field K]
  [AddCommGroup H] [Module K H] [AddCommGroup V] [Module K V]

theorem transportForm_rank (e : H ≃ₗ[K] V) (F : H →ₗ[K] Module.Dual K H) :
    Module.finrank K (LinearMap.range (transportForm e F)) =
      Module.finrank K (LinearMap.range F) := by
  unfold transportForm
  rw [LinearMap.range_comp,
    LinearMap.range_comp_of_range_eq_top F e.symm.range]
  exact e.symm.dualMap.finrank_map_eq (LinearMap.range F)

end Transport

section FunctionSpace

variable {Ω : Type*} (H : Submodule F2 (Ω → F2)) [FiniteDimensional F2 H]
  {ℓ m : Nat}

@[simp] theorem matrixForm_rank (F : H →ₗ[F2] Module.Dual F2 H) :
    Module.finrank F2 (LinearMap.range (matrixForm H F)) =
      Module.finrank F2 (LinearMap.range F) :=
  transportForm_rank (Module.evalEquiv F2 H) F

end FunctionSpace


open MixedSupport CanonicalKeys
open ProductEvaluation (displayedJoint )

end
end PerfectCompleteness.FunctionSpaceLowerRank

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

local instance lowerHFintype_ra6a25c_1 (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel) :
    Fintype (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) := Fintype.ofFinite _
attribute [local instance] OAI.PerfectCompleteness.HierarchicalLowerInverse.answerFintype
local instance upperDualFintype_ra6a25c_1 : Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  HierarchicalAllDecoderTables.upperDualFintype slots upper
theorem matrixTable_tested {r s : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r →
      Option (Answer slots upper lowerLevel d))
    (hvalid : DecoderTableAdmissibility.Admissible
      (HierarchicalAllDecoderTables.RowValid slots upper lowerLevel hbranch r d s) table)
    (X : HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d)
    (z : Answer slots upper lowerLevel d)
    (hz : matrixTable slots upper lowerLevel background d upperMatrix A table X = some z) :
    (LowerAffineSliceRank.testedGram
      (FunctionSpaceLowerRank.matrixForm
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) z)) X).rank ≤ 1 := by
  have h := hvalid
    (HierarchicalLowerMatrixInput.input slots upper lowerLevel background d upperMatrix A X)
    z hz
  have ht := h.2.1
  simpa only [HierarchicalLowerMatrixInput.input_testedMatrix] using ht

theorem matrixTable_high_rank {r s : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) r)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel r →
      Option (Answer slots upper lowerLevel d))
    (hvalid : DecoderTableAdmissibility.Admissible
      (HierarchicalAllDecoderTables.RowValid slots upper lowerLevel hbranch r d s) table)
    (X : HierarchicalLowerMatrixInput.Matrix (rows := rows) slots upper lowerLevel d)
    (z : Answer slots upper lowerLevel d)
    (hz : matrixTable slots upper lowerLevel background d upperMatrix A table X = some z) :
    s < Module.finrank F2 (LinearMap.range
      (FunctionSpaceLowerRank.matrixForm
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
        (OddListExtraction.multiplicationForm
          (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) z))) := by
  rw [FunctionSpaceLowerRank.matrixForm_rank]
  exact (hvalid
    (HierarchicalLowerMatrixInput.input slots upper lowerLevel background d upperMatrix A X)
    z hz).2.2

theorem matrixTable_agreement_lt_oai {r s m adviceRows : Nat}
    (d : HierarchicalFrozenTables.LowerNodes upper lowerLevel)
    (upperMatrix : HierarchicalMatrixTable.Matrix (rows := rows) slots upper)
    (A : ManyGoodRows.RowMap (Block rows upper) adviceRows)
    (table : HierarchicalAllDecoderTables.Input (rows := rows) slots upper lowerLevel adviceRows →
      Option (Answer slots upper lowerLevel d))
    (hvalid : DecoderTableAdmissibility.Admissible
      (HierarchicalAllDecoderTables.RowValid slots upper lowerLevel hbranch adviceRows d s) table)
    (ρ η : ℝ) (hm : 0 < m) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η)
    (hrows : 2 * m + r ≤ rows (Nodes.height (HierarchicalLeftDecoder.LowerNode upper lowerLevel d)))
    (herror : (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) ≤ ρ) :
    PartialTableInverse.nonzeroAgreement
      (matrixTable slots upper lowerLevel background d upperMatrix A table) < η := by
  let f := matrixTable slots upper lowerLevel background d upperMatrix A table
  let form := fun z : Answer slots upper lowerLevel d =>
    FunctionSpaceLowerRank.matrixForm
      (HierarchicalDecoderTables.LowerH slots upper lowerLevel d)
      (OddListExtraction.multiplicationForm
        (HierarchicalDecoderTables.LowerH slots upper lowerLevel d) z)
  have tested : ∀ X z, f X = some z → (LowerAffineSliceRank.testedGram (form z) X).rank ≤ 1 :=
    fun X z hz => matrixTable_tested slots upper lowerLevel background hbranch
      d upperMatrix A table hvalid X z hz
  have high : ∀ X z, f X = some z → s < Module.finrank F2 (LinearMap.range (form z)) :=
    fun X z hz => matrixTable_high_rank slots upper lowerLevel background hbranch
      d upperMatrix A table hvalid X z hz
  have h := LowerAffineSliceRank.high_rank_agreement_lt f form tested r s ρ η
    hm hρ hρ1 hconstants hrows herror
  have herase : MatrixErasure.erase f (fun X => ∃ z, f X = some z ∧
      Module.finrank F2 (LinearMap.range (form z)) ≤ s) = f := by
    funext X
    apply MatrixErasure.erase_eq_of_not
    rintro ⟨z, hz, hrank⟩
    exact (not_le_of_gt (high X z hz)) hrank
  rw [herase] at h
  exact h

end
end PerfectCompleteness.HierarchicalLowerInverse

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.HierarchicalLowerInverse.matrixTable_agreement_lt_oai := @OAI.PerfectCompleteness.HierarchicalLowerInverse.matrixTable_agreement_lt_oai
