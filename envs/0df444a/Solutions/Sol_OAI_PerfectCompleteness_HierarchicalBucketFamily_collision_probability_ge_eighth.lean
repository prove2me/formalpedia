-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalBucketFamily.collision_probability_ge_eighth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:14:09.723883+00:00
-- url     : https://prove2.me/submissions/ee968119-1932-4bfd-9f47-9ecdda0b48cd

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
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Definitions.Def_OAIQ252P015
import Theorems.Thm_OAI_PerfectCompleteness_RepresentativeBucketCollision_collision_probability_lower_bound

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact composition identities for finite distribution maps. -/
namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution
open scoped BigOperators
noncomputable section
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

theorem weight_eq_probability_singleton [DecidableEq A] (μ : FiniteDistribution A) (a : A) :
    μ.weight a = μ.probability (fun x => decide (x = a)) := by
  classical
  simp [probability]

theorem transport_eq_pushforward (μ : FiniteDistribution A) (e : A ≃ B) :
    μ.transport e = μ.pushforward e := by
  classical
  apply eq_of_weight_eq
  intro b
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton,
    probability_transport, probability_pushforward]

theorem expectation_pushforward (μ : FiniteDistribution A) (f : A → B) (h : B → ℝ) :
    (μ.pushforward f).expectation h = μ.expectation (fun a => h (f a)) := by
  classical
  simp only [expectation, pushforward, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp [ite_mul]

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_FactoredFunctionsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.FactoredFunctions

variable {𝕜 Ω Z I J : Type*} [Field 𝕜]

theorem const_mem_factoringSpace (other : Ω → Z) (c : 𝕜) :
    (fun _ : Ω => c) ∈ factoringSpace other := by
  intro x y _
  rfl

theorem one_mem_factoringSpace (other : Ω → Z) :
    (1 : Ω → 𝕜) ∈ factoringSpace other :=
  const_mem_factoringSpace other 1

theorem mul_mem_factoringSpace (other : Ω → Z) {f g : Ω → 𝕜}
    (hf : f ∈ factoringSpace other) (hg : g ∈ factoringSpace other) :
    f * g ∈ factoringSpace other := by
  intro x y h
  change f x * g x = f y * g y
  rw [hf x y h, hg x y h]

end PerfectCompleteness.FactoredFunctions



namespace PerfectCompleteness.FactoredFunctionsDependent

open PerfectCompleteness.FactoredFunctions

variable {𝕜 Ω I : Type*} [Field 𝕜] {J : I → Type*}

theorem coordinate_mem_factoringSpace (lower : Ω → (i : I) → J i → 𝕜)
    (i : I) (t : J i) :
    (fun x => lower x i t) ∈ factoringSpace lower := by
  intro x y h
  exact congrFun (congrFun h i) t

theorem dependentQuadraticSpan_le_factoringSpace (lower : Ω → (i : I) → J i → 𝕜) :
    dependentQuadraticSpan lower ≤ factoringSpace lower := by
  apply Submodule.span_le.mpr
  intro f hf
  rcases hf with rfl | ⟨i, t, u, rfl⟩
  · exact one_mem_factoringSpace lower
  · exact mul_mem_factoringSpace lower
      (coordinate_mem_factoringSpace lower i t) (coordinate_mem_factoringSpace lower i u)

end PerfectCompleteness.FactoredFunctionsDependent

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

theorem evaluate_update (ℓ : Nat) (eval : Ω → H) (t : Tape ℓ Ω)
    (a : Direction ℓ) (new : Ω) :
    evaluate ℓ eval (Function.update t a new) =
      evaluate ℓ eval t + rankOne a.val (eval new - eval (t a)) := by
  funext i
  let S : H := ∑ v : Direction ℓ, v.val i • eval (t v)
  let S' : H := ∑ v : Direction ℓ, v.val i • eval (Function.update t a new v)
  have hd : S' - S = a.val i • (eval new - eval (t a)) := by
    dsimp only [S', S]
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
    · rw [Function.update_self, smul_sub]
    · intro b _ hba
      simp only [Function.update_of_ne hba, sub_self]
    · intro ha
      exact (ha (Finset.mem_univ a)).elim
  change S' = S + a.val i • (eval new - eval (t a))
  simpa only [sub_add_cancel] using
    (congrArg (fun z : H => z + S) hd).trans (add_comm _ _)


open PointwiseSpaces RecursiveSpaces DescendantSpaces

universe u

end
end PerfectCompleteness.BucketSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BucketMatrixResampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketMatrixResampling

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)

variable {Ω : Type*} (V : Submodule F2 (Ω → F2))

theorem assembledMatrix_update (ℓ : Nat) (t : Tape ℓ V)
    (a : Direction ℓ) (new : V) :
    assembledMatrix V ℓ (Function.update t a new) =
      EvaluationMatrix.shift V (assembledMatrix V ℓ t) a.val (new - t a) := by
  unfold assembledMatrix
  rw [BucketSampler.evaluate_update]
  apply LinearMap.ext
  intro q
  funext i
  change q (BucketSampler.evaluate ℓ (id : V → V) t i + a.val i • (new - t a)) =
    q (BucketSampler.evaluate ℓ (id : V → V) t i) + q (new - t a) * a.val i
  simp only [map_add, map_smul, smul_eq_mul, mul_comm]

end
end PerfectCompleteness.BucketMatrixResampling

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_MatrixTriangularFoldingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



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

theorem determined_comap (B : Submodule F2 (Assignment slots → F2))
    (hB : B ≤ FactoredFunctions.factoringSpace other) :
    Determined slots H other (B.comap H.subtype) := by
  intro b x y h
  exact hB b.property x y h

end
end PerfectCompleteness.RepresentativeMatrixTable

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_DensityVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.DensityVariation

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias

noncomputable section

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem expectation_mul_const (μ : FiniteDistribution Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x * c) = μ.expectation f * c := by
  simp only [FiniteDistribution.expectation, ← mul_assoc, Finset.sum_mul]

theorem expectation_div (μ : FiniteDistribution Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expectation (fun x => f x / c) = μ.expectation f / c := by
  simpa only [div_eq_mul_inv] using expectation_mul_const μ f c⁻¹

end
end PerfectCompleteness.DensityVariation

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_CollisionAveragingLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

theorem average_square_bound (μ : FiniteDistribution B) (p collision : B → ℝ)
    (hlocal : ∀ b, p b ^ 2 / 2 ≤ collision b) :
    μ.expectation p ^ 2 / 2 ≤ μ.expectation collision := by
  calc
    _ ≤ μ.expectation (fun b => p b ^ 2) / 2 :=
      div_le_div_of_nonneg_right (mean_square_le μ p) (by norm_num)
    _ = μ.expectation (fun b => p b ^ 2 / 2) :=
      (DensityVariation.expectation_div μ (fun b => p b ^ 2) 2).symm
    _ ≤ μ.expectation collision := by
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hlocal b) (μ.nonnegative b)

theorem eighth_square_bound (μ : FiniteDistribution B) (p collision : B → ℝ)
    (hlocal : ∀ b, p b ^ 2 / 2 ≤ collision b)
    (c : ℝ) (hc : 0 ≤ c) (hmass : c / 2 ≤ μ.expectation p) :
    c ^ 2 / 8 ≤ μ.expectation collision := by
  have h := average_square_bound μ p collision hlocal
  have hprod : 0 ≤ (μ.expectation p - c / 2) * (μ.expectation p + c / 2) :=
    mul_nonneg (sub_nonneg.mpr hmass) (by linarith)
  nlinarith


end
end PerfectCompleteness.CollisionAveraging


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuarterBalanceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.SourceCoordinateSplit

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem coordinate_split (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (law P).transport (Equiv.piSplitAt i Ω) =
      (P i).product (law (fun j : {j : I // j ≠ i} => P j)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∏ j, (P j).weight ((Equiv.piSplitAt i Ω).symm y j)) =
    (P i).weight y.1 * ∏ j : {j : I // j ≠ i}, (P j).weight (y.2 j)
  calc
    _ = ∏ j, if h : j = i then (P i).weight y.1 else (P j).weight (y.2 ⟨j, h⟩) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp [Equiv.piSplitAt]
      · simp [Equiv.piSplitAt, hj]
    _ = _ := by
      rw [Fintype.prod_dite]
      simp

theorem coordinate_split_pushforward (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) :
    (law P).pushforward (fun x => (x i, fun j : {j : I // j ≠ i} => x j)) =
      (P i).product (law (fun j : {j : I // j ≠ i} => P j)) := by
  change (law P).pushforward (Equiv.piSplitAt i Ω) = _
  rw [← FiniteDistribution.transport_eq_pushforward]
  exact coordinate_split P i

end
end PerfectCompleteness.SourceCoordinateSplit



namespace PerfectCompleteness.FiniteProductSplit

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem split_law (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (FiniteProduct.law P).pushforward (Equiv.piSplitAt i Ω) =
      (P i).product (otherLaw P i) :=
  SourceCoordinateSplit.coordinate_split_pushforward P i

theorem expectation_split (P : (i : I) → FiniteDistribution (Ω i)) (i : I)
    (f : Ω i → Others (Ω := Ω) i → ℝ) :
    (FiniteProduct.law P).expectation (fun x => f (x i) (others i x)) =
      (P i).expectation (fun a => (otherLaw P i).expectation (fun b => f a b)) := by
  have h := congrArg (fun μ : FiniteDistribution (Ω i × Others (Ω := Ω) i) =>
    μ.expectation (fun z => f z.1 z.2)) (split_law P i)
  rw [FiniteDistribution.expectation_pushforward, FiniteDistribution.expectation_product] at h
  exact h

theorem expectation_background_first (P : (i : I) → FiniteDistribution (Ω i)) (i : I)
    (f : Ω i → Others (Ω := Ω) i → ℝ) :
    (FiniteProduct.law P).expectation (fun x => f (x i) (others i x)) =
      (otherLaw P i).expectation (fun b => (P i).expectation (fun a => f a b)) := by
  rw [expectation_split]
  exact FiniteDistribution.expectation_comm (P i) (otherLaw P i) f

theorem resampling_expectation (P : (i : I) → FiniteDistribution (Ω i)) (i : I)
    (f : Others (Ω := Ω) i → Ω i → Ω i → ℝ) :
    ((FiniteProduct.law P).product (P i)).expectation
        (fun z => f (others i z.1) (z.1 i) z.2) =
      (otherLaw P i).expectation
        (fun b => ((P i).product (P i)).expectation (fun z => f b z.1 z.2)) := by
  rw [FiniteDistribution.expectation_product]
  rw [expectation_background_first P i
    (fun a b => (P i).expectation (fun a' => f b a a'))]
  apply FiniteDistribution.expectation_congr
  intro b
  exact (FiniteDistribution.expectation_product (P i) (P i) (fun z => f b z.1 z.2)).symm

end
end PerfectCompleteness.FiniteProductSplit

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_BucketUsefulCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TreeSourceSpaces.slotDomainFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketUsefulCollision

noncomputable section

open scoped Classical
open ClauseSupport MixedSupport
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction Tape)

section Product

variable {H : Type*} {ℓ : Nat}

theorem fill_update (a : Direction ℓ)
    (b : FiniteProductSplit.Others (Ω := fun _ : Direction ℓ => H) a)
    (h h' : H) : Function.update (fill a b h) a h' = fill a b h' := by
  funext d
  by_cases hd : d = a
  · subst d
    simp [fill]
  · simp only [Function.update_of_ne hd, fill, dite_eq_right hd]

theorem fill_others (a : Direction ℓ) (t : Tape ℓ H) :
    fill a (FiniteProductSplit.others a t) (t a) = t := by
  funext d
  by_cases hd : d = a
  · subst d
    simp [fill]
  · simp only [fill, dite_eq_right hd, FiniteProductSplit.others]

theorem fill_others_update (a : Direction ℓ) (t : Tape ℓ H) (h : H) :
    fill a (FiniteProductSplit.others a t) h = Function.update t a h := by
  rw [← fill_update a (FiniteProductSplit.others a t) (t a) h, fill_others]

private theorem probability_eq_expectation {A : Type*} [Fintype A]
    (μ : FiniteDistribution A) (event : A → Bool) :
    μ.probability event = μ.expectation (fun x => if event x then 1 else 0) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    mul_ite, mul_one, mul_zero]

variable [Fintype H]

theorem probability_background_first (μ : FiniteDistribution H)
    (a : Direction ℓ) (event : Tape ℓ H → Bool) :
    (BucketSampler.tapeLaw ℓ μ).probability event =
      (FiniteProductSplit.otherLaw (fun _ : Direction ℓ => μ) a).expectation
        (fun b => μ.probability (fun h => event (fill a b h))) := by
  have h := FiniteProductSplit.expectation_background_first
    (fun _ : Direction ℓ => μ) a
    (fun h b => if event (fill a b h) then (1 : ℝ) else 0)
  simpa only [fill_others, ← probability_eq_expectation, BucketSampler.tapeLaw] using h

theorem probability_resampling (μ : FiniteDistribution H)
    (a : Direction ℓ) (event : Tape ℓ H → Tape ℓ H → Bool) :
    ((BucketSampler.tapeLaw ℓ μ).product μ).probability
        (fun z => event z.1 (Function.update z.1 a z.2)) =
      (FiniteProductSplit.otherLaw (fun _ : Direction ℓ => μ) a).expectation
        (fun b => (μ.product μ).probability
          (fun z => event (fill a b z.1) (fill a b z.2))) := by
  have h := FiniteProductSplit.resampling_expectation
    (fun _ : Direction ℓ => μ) a
    (fun b h h' => if event (fill a b h) (fill a b h') then (1 : ℝ) else 0)
  simp only [fill_others] at h
  simpa only [fill_others_update, ← probability_eq_expectation, BucketSampler.tapeLaw] using h

end Product


variable {n ℓ : Nat} {Z : Type*}
  (slots : Fin n → Slot) (V : Submodule F2 (Assignment slots → F2))
  (other : Assignment slots → Z) (σ : KeyStrategy.Strategy n)
  (W : Submodule F2 V) (s : (V ⧸ W) →ₗ[F2] V)

theorem assembledMatrix_fill (a : Direction ℓ)
    (b : FiniteProductSplit.Others (Ω := fun _ : Direction ℓ => V) a) (h : V) :
    BucketMatrixResampling.assembledMatrix V ℓ (fill a b h) =
      EvaluationMatrix.shift V
        (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0)) a.val h := by
  have he := BucketMatrixResampling.assembledMatrix_update V ℓ (fill a b 0) a h
  rw [fill_update] at he
  simpa only [fill_self, sub_zero] using he

variable [Fintype V] [Finite Z]

theorem collision_probability_lower_bound
    (hs : W.mkQ.comp s = LinearMap.id)
    (hW : RepresentativeMatrixTable.Determined slots V other W)
    (μ : FiniteDistribution V)
    (useful : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Prop)
    (a : Direction ℓ) :
    (BucketSampler.tapeLaw ℓ μ).probability
        (fun t => decide (CanonicalMatrixTable.Accepts slots V other σ a.val
          (BucketMatrixResampling.assembledMatrix V ℓ t)) &&
          (RepresentativeMatrixTable.partialTable slots V other σ W s useful
            (MatrixRowQuotient.projectMatrix W
              (BucketMatrixResampling.assembledMatrix V ℓ t))).isSome) ^ 2 / 2 ≤
      ((BucketSampler.tapeLaw ℓ μ).product μ).probability
        (fun z => TwoResponseCollision.collision
          (RepresentativeMatrixTable.partialTable slots V other σ W s useful)
          (MatrixRowQuotient.projectMatrix W
            (BucketMatrixResampling.assembledMatrix V ℓ z.1),
          MatrixRowQuotient.projectMatrix W
            (BucketMatrixResampling.assembledMatrix V ℓ (Function.update z.1 a z.2)))) := by
  let f := RepresentativeMatrixTable.partialTable slots V other σ W s useful
  let good : Tape ℓ V → Bool := fun t =>
    decide (CanonicalMatrixTable.Accepts slots V other σ a.val
      (BucketMatrixResampling.assembledMatrix V ℓ t)) &&
      (f (MatrixRowQuotient.projectMatrix W
        (BucketMatrixResampling.assembledMatrix V ℓ t))).isSome
  let collision : Tape ℓ V → Tape ℓ V → Bool := fun t t' =>
    TwoResponseCollision.collision f
      (MatrixRowQuotient.projectMatrix W (BucketMatrixResampling.assembledMatrix V ℓ t),
        MatrixRowQuotient.projectMatrix W (BucketMatrixResampling.assembledMatrix V ℓ t'))
  change (BucketSampler.tapeLaw ℓ μ).probability good ^ 2 / 2 ≤
    ((BucketSampler.tapeLaw ℓ μ).product μ).probability
      (fun z => collision z.1 (Function.update z.1 a z.2))
  rw [probability_background_first μ a good, probability_resampling μ a collision]
  apply CollisionAveraging.average_square_bound
  intro b
  have hgood : (fun h : V => good (fill a b h)) =
      TwoResponseCollision.goodDefined
        (RepresentativeBucketCollision.bucketTable slots V other σ W s useful a.val
          (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0)))
        (RepresentativeBucketCollision.bucketAccepted slots V other σ a.val
          (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0))) := by
    funext h
    dsimp only [good, f, TwoResponseCollision.goodDefined,
      RepresentativeBucketCollision.bucketTable, RepresentativeBucketCollision.bucketAccepted]
    simp only [assembledMatrix_fill slots V a b h]
  have htable (h : V) :
      f (MatrixRowQuotient.projectMatrix W
        (BucketMatrixResampling.assembledMatrix V ℓ (fill a b h))) =
      RepresentativeBucketCollision.bucketTable slots V other σ W s useful a.val
        (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0)) h := by
    dsimp only [f, RepresentativeBucketCollision.bucketTable]
    rw [assembledMatrix_fill slots V a b h]
  have hcollision :
      (fun z : V × V => collision (fill a b z.1) (fill a b z.2)) =
      TwoResponseCollision.collision
        (RepresentativeBucketCollision.bucketTable slots V other σ W s useful a.val
          (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0))) := by
    exact congrArg (fun g : V → Option ((Fin ℓ → F2) × Z) =>
      TwoResponseCollision.collision g) (funext htable)
  rw [hgood, hcollision]
  exact RepresentativeBucketCollision.collision_probability_lower_bound
    slots V other σ W s hs hW μ useful a.val a.property
      (BucketMatrixResampling.assembledMatrix V ℓ (fill a b 0))

end
end PerfectCompleteness.BucketUsefulCollision

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_GeometricPathLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.HierarchicalKnownRows

noncomputable section

open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat} {D : Type*}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)
  (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
  (descendant : D → {j : Nodes branch n // j ≠ upper})

theorem knownSpace_le_factoringSpace :
    knownSpace slots upper background descendant ≤
      FactoredFunctions.factoringSpace (HierarchicalMatrixTable.other slots upper background) := by
  intro f hf x y hxy
  apply FactoredFunctionsDependent.dependentQuadraticSpan_le_factoringSpace
    (lower slots upper background descendant) hf x y
  funext d i
  exact congrArg (fun z : HierarchicalMatrixTable.SideOutput (rows := rows) upper =>
    z.1 (descendant d) i) hxy

theorem determined :
    RepresentativeMatrixTable.Determined (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
      ((knownSpace slots upper background descendant).comap
        (NodeEmbedding.RowSpace slots upper).subtype) :=
  RepresentativeMatrixTable.determined_comap (TreeCanonical.numberedSlots slots)
    (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
    (knownSpace slots upper background descendant)
    (knownSpace_le_factoringSpace slots upper background descendant)

end
end PerfectCompleteness.HierarchicalKnownRows

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalFrozenTables

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

variable (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)

theorem determined :
    RepresentativeMatrixTable.Determined (TreeCanonical.numberedSlots slots)
      (NodeEmbedding.RowSpace slots upper) (HierarchicalMatrixTable.other slots upper background)
      (knownRows slots upper lowerLevel background) :=
  HierarchicalKnownRows.determined slots upper background (lowerIndex upper lowerLevel)

end
end PerfectCompleteness.HierarchicalFrozenTables



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_HierarchicalUsefulCollision
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalUsefulCollision

noncomputable section

open scoped BigOperators Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

private theorem probability_product {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A × B → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun a => ν.probability (fun b => event (a, b))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

private theorem probability_product_first {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A → Bool) :
    (μ.product ν).probability (fun x => event x.1) = μ.probability event := by
  unfold FiniteDistribution.probability
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  cases he : event a <;>
    simp [FiniteDistribution.product, he, ← Finset.mul_sum, ν.normalized]

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n)

variable {P : Type*} [Fintype P]

variable (lowerLevel : Nat) {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lower : Ω → Bool) (κ : ℝ)
  (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

attribute [local instance] OAI.PerfectCompleteness.HierarchicalUsefulCollision.backgroundFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalUsefulCollision.rowSpaceFintype
local instance valueFintype_rb2f041_1 :
    Fintype (Block rows upper × HierarchicalMatrixTable.SideOutput (rows := rows) upper) :=
  Fintype.ofFinite _
theorem direction_collision_lower_bound
    (background : Background (rows := rows) slots upper)
    (ν : FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (a : Direction (rows := rows) upper) :
    (BucketSampler.tapeLaw (rows (Nodes.height upper)) ν).probability
        (usefulAccepted slots upper lowerLevel original arrays lower κ σ background a) ^ 2 / 2 ≤
      ((BucketSampler.tapeLaw (rows (Nodes.height upper)) ν).product ν).probability
        (fun z => HierarchicalAgreementMean.collision slots upper lowerLevel
          original arrays lower κ σ
          (HierarchicalAgreementMean.pairRecord slots upper (background, (a, z)))) := by
  exact BucketUsefulCollision.collision_probability_lower_bound
    (TreeCanonical.numberedSlots slots) (NodeEmbedding.RowSpace slots upper)
    (HierarchicalMatrixTable.other slots upper background) σ
    (HierarchicalFrozenTables.knownRows slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap slots upper lowerLevel background)
    (HierarchicalFrozenTables.sectionMap_spec slots upper lowerLevel background)
    (HierarchicalFrozenTables.determined slots upper lowerLevel background) ν
    (fun X => HierarchicalUsefulness.mark slots upper lowerLevel original arrays lower κ
      ⟨background, X⟩ = true) a

theorem useful_probability_eq
    (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (law slots upper externalLaw scalarLaw hrows).probability
        (usefulEvent slots upper lowerLevel original arrays lower κ σ background) =
      externalLaw.expectation (fun p => (directionLaw upper hrows).expectation (fun a =>
        (BucketSampler.tapeLaw (rows (Nodes.height upper)) (scalarLaw p)).probability
          (usefulAccepted slots upper lowerLevel original arrays lower κ σ (background p) a))) := by
  rw [law, CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro p
  rw [bucketLaw, probability_product]
  apply FiniteDistribution.expectation_congr
  intro a
  exact probability_product_first
    (BucketSampler.tapeLaw (rows (Nodes.height upper)) (scalarLaw p)) (scalarLaw p)
    (usefulAccepted slots upper lowerLevel original arrays lower κ σ (background p) a)

theorem collision_probability_eq
    (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (pairLaw slots upper externalLaw background scalarLaw hrows).probability
        (HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ) =
      externalLaw.expectation (fun p => (directionLaw upper hrows).expectation (fun a =>
        ((BucketSampler.tapeLaw (rows (Nodes.height upper)) (scalarLaw p)).product
          (scalarLaw p)).probability (fun z =>
            HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ
              (HierarchicalAgreementMean.pairRecord slots upper (background p, (a, z)))))) := by
  rw [pairLaw, FiniteDistribution.probability_pushforward, law,
    CompletionSoundness.sigmaLaw_probability]
  apply FiniteDistribution.expectation_congr
  intro p
  exact probability_product (directionLaw upper hrows)
    ((BucketSampler.tapeLaw (rows (Nodes.height upper)) (scalarLaw p)).product (scalarLaw p))
    (fun z => HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ
      (HierarchicalAgreementMean.pairRecord slots upper (background p, z)))

theorem collision_probability_lower_bound
    (externalLaw : FiniteDistribution P)
    (background : P → Background (rows := rows) slots upper)
    (scalarLaw : P → FiniteDistribution (NodeEmbedding.RowSpace slots upper))
    (hrows : 0 < rows (Nodes.height upper)) :
    (law slots upper externalLaw scalarLaw hrows).probability
        (usefulEvent slots upper lowerLevel original arrays lower κ σ background) ^ 2 / 2 ≤
      (pairLaw slots upper externalLaw background scalarLaw hrows).probability
        (HierarchicalAgreementMean.collision slots upper lowerLevel original arrays lower κ σ) := by
  rw [useful_probability_eq, collision_probability_eq]
  apply CollisionAveraging.average_square_bound
  intro p
  apply CollisionAveraging.average_square_bound
  intro a
  exact direction_collision_lower_bound slots upper lowerLevel original arrays lower κ σ
    (background p) (scalarLaw p) a

end
end PerfectCompleteness.HierarchicalUsefulCollision

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_HierarchicalBucketFamily
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.HierarchicalBucketFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

variable {P : O → Type*} [∀ o, Fintype (P o)]

attribute [local instance] OAI.PerfectCompleteness.HierarchicalBucketFamily.backgroundFiberFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalBucketFamily.rowSpaceFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalBucketFamily.inputFintype
local instance valueFintype_rb2f041_2 (b : HierarchicalAdviceFamily.Background S) :
    Fintype (HierarchicalAdviceFamily.Value S b) :=
  HierarchicalAdviceFamily.valueFintype S b
variable (κ : ℝ) (outer : FiniteDistribution O)
  (externalLaw : (o : O) → FiniteDistribution (P o))
  (background : (o : O) → P o → HierarchicalAdviceExperiment.Background (S o))
  (scalarLaw : (o : O) → P o →
    FiniteDistribution (NodeEmbedding.RowSpace (S o).slots (S o).upper))
  (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))

theorem collision_probability_ge_eighth_oai (c : ℝ) (hc : 0 ≤ c)
    (hmass : c / 2 ≤ usefulMass S κ outer externalLaw background scalarLaw hrows) :
    c ^ 2 / 8 ≤
      (actualPairLaw S outer externalLaw background scalarLaw hrows).probability (collision S κ) := by
  rw [actualPairLaw, CompletionSoundness.sigmaLaw_probability]
  refine CollisionAveraging.eighth_square_bound outer
    (fun o => HierarchicalAdviceFromBuckets.usefulProbability (S o) κ
      (externalLaw o) (background o) (scalarLaw o) (hrows o)) _ ?_ c hc hmass
  intro o
  exact HierarchicalUsefulCollision.collision_probability_lower_bound
    (S o).slots (S o).upper (S o).lowerLevel (S o).original (S o).arrays
    (HierarchicalAdviceExperiment.lowerEvent (S o)) κ (S o).strategy
    (externalLaw o) (background o) (scalarLaw o) (hrows o)

end
end PerfectCompleteness.HierarchicalBucketFamily

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.PerfectCompleteness.HierarchicalBucketFamily.collision_probability_ge_eighth_oai.{u_1, u_2, u_3} := @OAI.PerfectCompleteness.HierarchicalBucketFamily.collision_probability_ge_eighth_oai.{u_1, u_2, u_3}
