-- Prove2me | solution 1 for OAI.PerfectCompleteness.BucketQuotientAgreement.directionCollision_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:29.180629+00:00
-- url     : https://prove2.me/submissions/b2ebe3f5-c732-4407-b113-e82bd04d7353

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
import Mathlib.Data.Fin.Tuple.Basic
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
import Definitions.Def_OAIQ252P008

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_ValueLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
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
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_KernelSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

/-- Applying separate maps to independent samples preserves their independence. -/
theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

end FiniteDistribution

end
end UniqueGamesTheorem.Foundations.Games

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_UniformLinearImage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UniformLinearImage

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem eq_uniform_of_weight_constant {A : Type*} [Fintype A] [Nonempty A]
    (μ : FiniteDistribution A) (constant : ∀ x y, μ.weight x = μ.weight y) :
    μ = FiniteDistribution.uniform A := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change μ.weight x = 1 / (Fintype.card A : ℝ)
  apply (eq_div_iff (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)).mpr
  calc
    μ.weight x * (Fintype.card A : ℝ) = ∑ _y : A, μ.weight x := by
      simp [mul_comm]
    _ = ∑ y : A, μ.weight y := by
      apply Finset.sum_congr rfl
      intro y _
      exact constant x y
    _ = 1 := μ.normalized

theorem uniform_pushforward_weight {A B : Type*} [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] (f : A → B) (y : B) :
    ((FiniteDistribution.uniform A).pushforward f).weight y =
      ((Finset.univ.filter (fun x => f x = y)).card : ℝ) / Fintype.card A := by
  classical
  calc
    _ = ∑ x : A, if f x = y then (1 / (Fintype.card A : ℝ)) else 0 := by
      unfold FiniteDistribution.pushforward FiniteDistribution.uniform
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : f x = y <;> simp [h]
    _ = _ := by
      rw [← Finset.sum_filter]
      simp [nsmul_eq_mul, div_eq_mul_inv]

theorem uniform_pushforward_addHom {A B : Type*}
    [AddGroup A] [AddMonoid B] [Fintype A] [Fintype B]
    (f : A →+ B) (surjective : Function.Surjective f) :
    (FiniteDistribution.uniform A).pushforward f = FiniteDistribution.uniform B := by
  classical
  apply eq_uniform_of_weight_constant
  intro y z
  rw [uniform_pushforward_weight, uniform_pushforward_weight,
    AddMonoidHom.card_fiber_eq_of_mem_range f (surjective y) (surjective z)]

theorem uniform_pushforward_linearMap {R A B : Type*} [Semiring R]
    [AddCommGroup A] [AddCommMonoid B] [Module R A] [Module R B]
    [Fintype A] [Fintype B] (f : A →ₗ[R] B) (surjective : Function.Surjective f) :
    (FiniteDistribution.uniform A).pushforward f = FiniteDistribution.uniform B :=
  uniform_pushforward_addHom f.toAddMonoidHom surjective

section Product

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

variable {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]
  [∀ i, AddCommGroup (Ω i)] [∀ i, Module R (Ω i)]

variable [Fintype V]

theorem product_uniform_linear_image (f : ((i : I) → Ω i) →ₗ[R] V)
    (surjective : Function.Surjective f) :
    (FiniteProduct.law (fun i => FiniteDistribution.uniform (Ω i))).pushforward f =
      FiniteDistribution.uniform V := by
  rw [law_uniform]
  exact uniform_pushforward_linearMap f surjective

end Product
end
end PerfectCompleteness.UniformLinearImage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketSampler
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformDifference
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.ReducedPartition.instNonemptyPart _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.UniformDifference

noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

variable {B H : Type*} [Fintype B] [Fintype H] [AddGroup H]

theorem expectation_difference (μ : FiniteDistribution B) (old : B → H)
    (f : B × H → ℝ) :
    (μ.product (FiniteDistribution.uniform H)).expectation
        (fun p => f (difference old p)) =
      (μ.product (FiniteDistribution.uniform H)).expectation f := by
  rw [FiniteDistribution.expectation_product, FiniteDistribution.expectation_product]
  apply FiniteDistribution.expectation_congr
  intro b
  rw [FiniteDistribution.expectation_uniform, FiniteDistribution.expectation_uniform]
  simpa only [Fintype.expect_eq_sum_div_card, difference, sub_eq_add_neg] using
    Fintype.expect_equiv (Equiv.addRight (-old b))
      (fun h : H => f (b, h - old b)) (fun h : H => f (b, h))
      (fun _ => by simp only [sub_eq_add_neg]; rfl)

theorem difference_law (μ : FiniteDistribution B) (old : B → H) :
    (μ.product (FiniteDistribution.uniform H)).pushforward (difference old) =
      μ.product (FiniteDistribution.uniform H) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  have h := expectation_difference μ old (fun p => if p = z then (1 : ℝ) else 0)
  rw [← FiniteDistribution.expectation_pushforward
    (μ.product (FiniteDistribution.uniform H)) (difference old)
    (fun p => if p = z then (1 : ℝ) else 0)] at h
  simpa only [FiniteDistribution.expectation, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, if_true] using h

theorem observed_difference_law {P : Type*} [Fintype P]
    (μ : FiniteDistribution B) (old : B → H) (observe : B → P) :
    (μ.product (FiniteDistribution.uniform H)).pushforward
        (fun p => (observe p.1, p.2 - old p.1)) =
      (μ.product (FiniteDistribution.uniform H)).pushforward
        (fun p => (observe p.1, p.2)) := by
  have h := congrArg
    (fun ν : FiniteDistribution (B × H) => ν.pushforward (fun p => (observe p.1, p.2)))
    (difference_law μ old)
  rw [FiniteDistribution.pushforward_comp] at h
  exact h

end
end PerfectCompleteness.UniformDifference

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketUniformLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BucketUniform

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open BucketSampler (F2 Direction)

variable {H : Type*} [AddCommGroup H] [Module F2 H]

theorem evaluate_single {ℓ : Nat} (v : Direction ℓ) (h : H) :
    evaluateLinear ℓ (Pi.single v h) = BucketSampler.rankOne v.val h := by
  funext i
  change (∑ w : Direction ℓ, w.val i • (Pi.single v h) w) = v.val i • h
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _ hw
    simp [hw]
  · intro hv
    exact (hv (Finset.mem_univ v)).elim

theorem evaluate_coordinate_bucket {ℓ : Nat} (i : Fin ℓ) (h : H) :
    evaluateLinear ℓ (Pi.single (coordinateDirection i) h) = Pi.single i h := by
  rw [evaluate_single]
  funext j
  by_cases hij : i = j
  · subst j
    simp [BucketSampler.rankOne, coordinateDirection]
  · simp [BucketSampler.rankOne, coordinateDirection, Ne.symm hij]

theorem evaluate_coordinateTape {ℓ : Nat} (rows : Fin ℓ → H) :
    evaluateLinear ℓ (coordinateTape rows) = rows := by
  unfold coordinateTape
  rw [map_sum]
  simp only [evaluate_coordinate_bucket, Finset.univ_sum_single]

theorem evaluateLinear_surjective (ℓ : Nat) :
    Function.Surjective (evaluateLinear (H := H) ℓ) :=
  fun rows => ⟨coordinateTape rows, evaluate_coordinateTape rows⟩

theorem uniform_evaluate_law [Fintype H] (ℓ : Nat) :
    (BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform H)).pushforward
        (BucketSampler.evaluate ℓ (id : H → H)) =
      FiniteDistribution.uniform (Fin ℓ → H) :=
  UniformLinearImage.product_uniform_linear_image
    (I := Direction ℓ) (Ω := fun _ => H) (R := F2) (V := Fin ℓ → H)
    (evaluateLinear (H := H) ℓ) (evaluateLinear_surjective (H := H) ℓ)


variable {Ω : Type*} (V : Submodule F2 (Ω → F2))

theorem ofRowsLinear_surjective [FiniteDimensional F2 V] (ℓ : Nat) :
    Function.Surjective (ofRowsLinear V ℓ) :=
  fun X => ⟨EvaluationMatrix.rows V X, EvaluationMatrix.ofRows_rows V X⟩

theorem uniform_matrix_law (ℓ : Nat) [Fintype V] [FiniteDimensional F2 V]
    [Fintype (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2))] :
    (BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).pushforward
        (fun t => EvaluationMatrix.ofRows V (BucketSampler.evaluate ℓ (id : V → V) t)) =
      FiniteDistribution.uniform (Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2)) := by
  calc
    _ = ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).pushforward
        (BucketSampler.evaluate ℓ (id : V → V))).pushforward
          (EvaluationMatrix.ofRows V) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (FiniteDistribution.uniform (Fin ℓ → V)).pushforward
        (EvaluationMatrix.ofRows V) := by rw [uniform_evaluate_law]
    _ = _ := UniformLinearImage.uniform_pushforward_linearMap
      (ofRowsLinear V ℓ) (ofRowsLinear_surjective V ℓ)

end
end PerfectCompleteness.BucketUniform



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BucketMatrixResampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true
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

private theorem pushforward_id {A : Type*} [Fintype A] (μ : FiniteDistribution A) :
    μ.pushforward (fun a => a) = μ := by
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  simp [FiniteDistribution.pushforward]


variable (ℓ : Nat) [Fintype V] [Fintype (Matrix V ℓ)]

theorem matrix_difference_law (μ : FiniteDistribution (Tape ℓ V)) (a : Direction ℓ) :
    (μ.product (FiniteDistribution.uniform V)).pushforward
        (fun p => (assembledMatrix V ℓ p.1, p.2 - p.1 a)) =
      (μ.pushforward (assembledMatrix V ℓ)).product (FiniteDistribution.uniform V) := by
  rw [UniformDifference.observed_difference_law μ (fun t => t a)
    (assembledMatrix V ℓ)]
  have hp := FiniteDistribution.product_pushforward μ
    (FiniteDistribution.uniform V) (assembledMatrix V ℓ) (id : V → V)
  have hi : (FiniteDistribution.uniform V).pushforward (id : V → V) =
      FiniteDistribution.uniform V :=
    pushforward_id (FiniteDistribution.uniform V)
  rw [hi] at hp
  simpa only [id_eq] using hp

theorem resampled_matrix_pair_law (μ : FiniteDistribution (Tape ℓ V)) (a : Direction ℓ) :
    (μ.product (FiniteDistribution.uniform V)).pushforward
        (fun p => (assembledMatrix V ℓ p.1,
          assembledMatrix V ℓ (Function.update p.1 a p.2))) =
      ((μ.pushforward (assembledMatrix V ℓ)).product (FiniteDistribution.uniform V)).pushforward
        (fun p => (p.1, EvaluationMatrix.shift V p.1 a.val p.2)) := by
  have h := congrArg
    (fun ν : FiniteDistribution (Matrix V ℓ × V) => ν.pushforward
      (fun p => (p.1, EvaluationMatrix.shift V p.1 a.val p.2)))
    (matrix_difference_law V ℓ μ a)
  rw [FiniteDistribution.pushforward_comp] at h
  simpa only [assembledMatrix_update] using h

variable [FiniteDimensional F2 V]

theorem uniform_assembledMatrix_law :
    (BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).pushforward
        (assembledMatrix V ℓ) = FiniteDistribution.uniform (Matrix V ℓ) :=
  BucketUniform.uniform_matrix_law V ℓ

theorem uniform_resampled_matrix_pair_law (a : Direction ℓ) :
    ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
        (FiniteDistribution.uniform V)).pushforward
        (fun p => (assembledMatrix V ℓ p.1,
          assembledMatrix V ℓ (Function.update p.1 a p.2))) =
      ((FiniteDistribution.uniform (Matrix V ℓ)).product
        (FiniteDistribution.uniform V)).pushforward
          (fun p => (p.1, EvaluationMatrix.shift V p.1 a.val p.2)) := by
  rw [resampled_matrix_pair_law, uniform_assembledMatrix_law]

theorem uniform_resampled_event_probability (a : Direction ℓ)
    (event : Matrix V ℓ × Matrix V ℓ → Bool) :
    ((BucketSampler.tapeLaw ℓ (FiniteDistribution.uniform V)).product
        (FiniteDistribution.uniform V)).probability
        (fun p => event (assembledMatrix V ℓ p.1,
          assembledMatrix V ℓ (Function.update p.1 a p.2))) =
      ((FiniteDistribution.uniform (Matrix V ℓ)).product
        (FiniteDistribution.uniform V)).probability
          (fun p => event (p.1, EvaluationMatrix.shift V p.1 a.val p.2)) := by
  have h := congrArg (fun ν => FiniteDistribution.probability ν event)
    (uniform_resampled_matrix_pair_law V ℓ a)
  simpa only [FiniteDistribution.probability_pushforward] using h

end
end PerfectCompleteness.BucketMatrixResampling

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_BucketQuotientAgreement
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.DecoderTableCoupling.definedEqual_collision _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true
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
open PartialTableInverse (definedEquality )

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

private theorem expectation_uniform_eq_expect {A : Type*} [Fintype A] [Nonempty A]
    (f : A → ℝ) :
    (FiniteDistribution.uniform A).expectation f = 𝔼 x : A, f x := by
  rw [FiniteDistribution.expectation_uniform, Fintype.expect_eq_sum_div_card]

variable {Ω Y : Type*} [Fintype Y]
  (V : Submodule F2 (Ω → F2)) [Fintype V] [FiniteDimensional F2 V]
  (ℓ : Nat) (W : Submodule F2 V)

theorem directionCollision_eq_oai
    (f : (Module.Dual F2 (V ⧸ W) →ₗ[F2] (Fin ℓ → F2)) → Option Y)
    (a : Direction ℓ) :
    directionCollision V ℓ W f a =
      𝔼 X : Module.Dual F2 V →ₗ[F2] (Fin ℓ → F2), 𝔼 h : V,
        definedEquality f (MatrixRowQuotient.projectMatrix W X)
          (MatrixRowQuotient.projectMatrix W (EvaluationMatrix.shift V X a.val h)) := by
  unfold directionCollision
  rw [BucketMatrixResampling.uniform_resampled_event_probability V ℓ a
    (fun p => TwoResponseCollision.collision f
      (MatrixRowQuotient.projectMatrix W p.1, MatrixRowQuotient.projectMatrix W p.2))]
  rw [probability_collision_eq_expectation, FiniteDistribution.expectation_product]
  simp only [expectation_uniform_eq_expect]

end
end PerfectCompleteness.BucketQuotientAgreement

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PerfectCompleteness.BucketQuotientAgreement.directionCollision_eq_oai.{u_1, u_2} := @OAI.PerfectCompleteness.BucketQuotientAgreement.directionCollision_eq_oai.{u_1, u_2}
