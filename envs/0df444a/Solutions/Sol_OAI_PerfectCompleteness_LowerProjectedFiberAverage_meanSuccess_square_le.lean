-- Prove2me | solution 1 for OAI.PerfectCompleteness.LowerProjectedFiberAverage.meanSuccess_square_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:18:59.99058+00:00
-- url     : https://prove2.me/submissions/40bd1f08-aad3-4553-9577-1282f56f0f88

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
import Theorems.Thm_OAI_PerfectCompleteness_LowerProjectedFiberAverage_rawCollision_eq_mean
import Theorems.Thm_OAI_PerfectCompleteness_ProjectedFiberSquare_success_square_le

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

theorem expectation_comm (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → Γ → ℝ) :
    μ.expectation (fun x => ν.expectation (f x)) =
      ν.expectation (fun y => μ.expectation (fun x => f x y)) := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  exact mul_left_comm _ _ _

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
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_SamplingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-!
Finite real probability vectors and information inequalities.

`relativeEntropy` uses the natural logarithm and a real-valued finite sum.
Its theorems require support containment, so a positive numerator is never
silently assigned finite divergence against a zero denominator.
-/

namespace UniqueGamesTheorem.Foundations.Information

open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- Finite weighted Cauchy–Schwarz for probability weights. The summands
need not be nonnegative. -/
theorem weighted_sum_sq_le (w x : α → ℝ) (hw : IsProbability w) :
    (∑ a, w a * x a)^2 ≤ ∑ a, w a * (x a)^2 := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset α)
    (fun a => Real.sqrt (w a)) (fun a => Real.sqrt (w a) * x a)
  have hfirst : ∀ a, Real.sqrt (w a) * (Real.sqrt (w a) * x a) = w a * x a := by
    intro a
    rw [← mul_assoc, Real.mul_self_sqrt (hw.1 a)]
  have hsecond : ∀ a, (Real.sqrt (w a) * x a)^2 = w a * (x a)^2 := by
    intro a
    rw [mul_pow, Real.sq_sqrt (hw.1 a)]
  simpa only [hfirst, hsecond, Real.sq_sqrt (hw.1 _), hw.2, one_mul] using hcs

end UniqueGamesTheorem.Foundations.Information

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CollisionAveragingLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.CollisionAveraging

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

variable {B : Type*} [Fintype B]

theorem mean_square_le (μ : FiniteDistribution B) (p : B → ℝ) :
    μ.expectation p ^ 2 ≤ μ.expectation (fun b => p b ^ 2) :=
  UniqueGamesTheorem.Foundations.Information.weighted_sum_sq_le μ.weight p
    ⟨μ.nonnegative, μ.normalized⟩

end
end PerfectCompleteness.CollisionAveraging


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_ProjectedFiberUpperSeed
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.ProjectedFiberUpperSeed

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open ProjectedLowerFiber ProjectedFiberSquare

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots projected : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (level : Nat)
  (d : HierarchicalFrozenTables.LowerNodes upper level)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)
  (a : Direction (rows := rows) upper level d) (arrays : Arrays projected rows)
  (known : HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
    OwnInputReference.UpperSpace projected upper)
  (repeats : Nat → Nat) (cut : OwnInputReference.Cut upper (lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

local instance rowSpaceFintype_rc10e5c_1 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_rc10e5c_1 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
theorem seed_mean_ignore_right (f : UpperTable (rows := rows) slots upper level r → ℝ) :
    (seedLaw slots projected upper level d A a arrays known repeats cut σ useful ρ threshold).expectation
        (fun seed => f seed.1) =
      (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation f := by
  unfold seedLaw
  rw [FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro table
  unfold FiniteDistribution.expectation
  change (∑ x, (rightLaw projected upper level d A a arrays known repeats cut σ threshold).weight x *
    f table) = f table
  rw [← Finset.sum_mul,
    (rightLaw projected upper level d A a arrays known repeats cut σ threshold).normalized,
    one_mul]

variable (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (hbranch : ∀ k < n, 0 < branch k)

theorem success_square_le_upperSeed (s : Nat)
    (ν : FiniteDistribution (Scalar projected upper level d)) :
    success slots projected projection upper level hbranch d A a arrays known
        repeats cut σ useful ρ threshold s ν ^ 2 ≤
      (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation
        (fun table => (ν.product ν).probability
          (restrictedPair slots projected projection upper level hbranch d A a arrays s table)) := by
  have h := success_square_le slots projected projection upper level hbranch d A a arrays known
    repeats cut σ useful ρ threshold s ν
  calc
    _ ≤ _ := h
    _ = _ := seed_mean_ignore_right slots projected upper level d A a arrays known
      repeats cut σ useful ρ threshold (fun table => (ν.product ν).probability
        (restrictedPair slots projected projection upper level hbranch d A a arrays s table))

end
end PerfectCompleteness.ProjectedFiberUpperSeed

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_LowerProjectedFiberAverage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalOwnBucketSplit.otherIndexFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorFintype _root_.OAI.PerfectCompleteness.OriginalWholeCutTape.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instDecidableEqTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerBody.instFintypeTape _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.LowerProjectedFiberAverage

noncomputable section

open scoped Classical
open RecursiveSpaces DescendantSpaces TreeSourceSpaces HierarchicalArrays
open WholeCutGrouping
open UniqueGamesTheorem.Foundations.Games

attribute [local instance] RightDecoder.scalarFintype

variable {branch rows repeats : Nat → Nat} {n m t : Nat}
  (path : Path branch n (m + 1))
  (slots projected : Slots branch n → Fin t → MixedSupport.Slot)
  (projection : ∀ leaf j, MixedSupport.Projection (slots leaf j) (projected leaf j))
  (upper : Nodes branch n) (level : Nat)
  (hbranch : ∀ k < n, 0 < branch k)
  (d : HierarchicalFrozenTables.LowerNodes upper level)
  (hnode : WholeArrayInteriorExterior.upperNode path =
    HierarchicalLeftDecoder.LowerNode upper level d)
  (a : BucketSampler.Direction (rows (m + 1)))
  (exterior : Exterior rows repeats path projected)

variable {r : Nat} (A : ManyGoodRows.RowMap (Block rows upper) r)

variable
  (known : Background path projected a → HiddenBucketBias.VisibleDirection (LinearMap.ker A) →
    OwnInputReference.UpperSpace projected upper)
  (cut : OwnInputReference.Cut upper (ProjectedLowerFiber.lower upper level d))
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (useful : (bg : HierarchicalMatrixTable.Background (rows := rows) slots upper) →
    HierarchicalFrozenTables.QuotientMatrix slots upper level bg → Prop)
  (ρ threshold : ℝ)

local instance rowSpaceFintype_rc10e5c_2 : Fintype (NodeEmbedding.RowSpace slots upper) :=
  Fintype.ofFinite _
local instance upperAnswerFintype_rc10e5c_2 :
    Fintype (HierarchicalAllDecoderTables.UpperAnswer slots upper) :=
  LeftDecoder.dualFintype (V := NodeEmbedding.RowSpace slots upper)
theorem meanSuccess_square_le_oai (s : Nat) :
    meanSuccess path slots projected projection upper level hbranch d hnode a exterior A
        known cut σ useful ρ threshold s ^ 2 ≤
      (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation
        (rawCollision path slots projected projection upper level hbranch d a exterior A s) := by
  unfold meanSuccess
  apply (CollisionAveraging.mean_square_le _ _).trans
  calc
    _ ≤ (backgroundLaw path projected a).expectation (fun bg =>
        (HierarchicalAllDecoderTables.upperTableLaw slots upper level σ useful r ρ).expectation
          (fun table =>
            ((FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d)).product
              (FiniteDistribution.uniform (ProjectedLowerFiber.Scalar projected upper level d))).probability
                (ProjectedFiberSquare.restrictedPair slots projected projection upper level hbranch d A
                  (ProjectedFiberRawPair.direction path upper level d hnode a)
                  (baseline path projected a exterior bg) s table))) := by
      apply Finset.sum_le_sum
      intro bg _
      exact mul_le_mul_of_nonneg_left
        (ProjectedFiberUpperSeed.success_square_le_upperSeed slots projected upper level d A
          (ProjectedFiberRawPair.direction path upper level d hnode a)
          (baseline path projected a exterior bg) (known bg) repeats cut σ useful ρ threshold
          projection hbranch s (FiniteDistribution.uniform
            (ProjectedLowerFiber.Scalar projected upper level d)))
        ((backgroundLaw path projected a).nonnegative bg)
    _ = _ := by
      rw [FiniteDistribution.expectation_comm]
      apply FiniteDistribution.expectation_congr
      intro table
      exact (rawCollision_eq_mean path slots projected projection upper level hbranch d hnode a
        exterior A s table).symm

end
end PerfectCompleteness.LowerProjectedFiberAverage

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.LowerProjectedFiberAverage.meanSuccess_square_le_oai := @OAI.PerfectCompleteness.LowerProjectedFiberAverage.meanSuccess_square_le_oai
