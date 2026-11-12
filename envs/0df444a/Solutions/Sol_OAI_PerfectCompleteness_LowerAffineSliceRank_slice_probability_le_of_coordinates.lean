-- Prove2me | solution 1 for OAI.PerfectCompleteness.LowerAffineSliceRank.slice_probability_le_of_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:13:41.649689+00:00
-- url     : https://prove2.me/submissions/8c803def-d6aa-428a-9339-c45a09d44119

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
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
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
import Definitions.Def_OAIQ252P011

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_BilinearGramCompressionLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BilinearGramCompression

open scoped BigOperators

noncomputable section

variable {K H R I J : Type*} [Field K] [AddCommGroup H] [Module K H]
  [Fintype R] [Fintype I] [Fintype J]

omit [Fintype I] [Fintype J] in
theorem crossGram_combinations (F : H →ₗ[K] Module.Dual K H) (rows : R → H)
    (T : Matrix I R K) (S : Matrix J R K) :
    crossGram F (combinations rows T) (combinations rows S) =
      T * gram F rows * S.transpose := by
  classical
  ext i j
  simp only [crossGram, combinations, gram, map_sum, map_smul,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro r _
  ac_rfl

omit [Fintype I] in
theorem cross_rank_le (F : H →ₗ[K] Module.Dual K H) (rows : R → H)
    (T : Matrix I R K) (S : Matrix J R K) :
    (crossGram F (combinations rows T) (combinations rows S)).rank ≤
      (gram F rows).rank := by
  rw [crossGram_combinations]
  exact (Matrix.rank_mul_le_left (T * gram F rows) S.transpose).trans
    (Matrix.rank_mul_le_right T (gram F rows))

end
end PerfectCompleteness.BilinearGramCompression

end

section

namespace PerfectCompleteness.BilinearRestrictionRank

noncomputable section

open Module

variable {𝕜 H V U : Type*} [Field 𝕜]
  [AddCommGroup H] [Module 𝕜 H]
  [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup U] [Module 𝕜 U]

theorem ker_domRestrict_finrank_le [FiniteDimensional 𝕜 H]
    (f : H →ₗ[𝕜] V) (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.ker (f.domRestrict N)) ≤ finrank 𝕜 (LinearMap.ker f) := by
  let inclusion : LinearMap.ker (f.domRestrict N) →ₗ[𝕜] LinearMap.ker f :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply LinearMap.finrank_le_finrank_of_injective (f := inclusion)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : LinearMap.ker f => (z : H)) h

theorem rank_domRestrict_add_codim [FiniteDimensional 𝕜 H]
    (f : H →ₗ[𝕜] V) (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.range f) ≤
      finrank 𝕜 (LinearMap.range (f.domRestrict N)) + finrank 𝕜 (H ⧸ N) := by
  have hwhole := f.finrank_range_add_finrank_ker
  have hrestricted := (f.domRestrict N).finrank_range_add_finrank_ker
  have hquotient := N.finrank_quotient_add_finrank
  have hkernel := ker_domRestrict_finrank_le f N
  omega

theorem rank_le_rank_comp_add_ker [FiniteDimensional 𝕜 V]
    (g : H →ₗ[𝕜] V) (f : V →ₗ[𝕜] U) :
    finrank 𝕜 (LinearMap.range g) ≤
      finrank 𝕜 (LinearMap.range (f.comp g)) + finrank 𝕜 (LinearMap.ker f) := by
  have hrange : LinearMap.range (f.domRestrict (LinearMap.range g)) =
      LinearMap.range (f.comp g) := by
    rw [LinearMap.range_domRestrict, LinearMap.range_comp]
  have hrank := (f.domRestrict (LinearMap.range g)).finrank_range_add_finrank_ker
  rw [hrange] at hrank
  have hkernel := ker_domRestrict_finrank_le f (LinearMap.range g)
  omega

theorem dualRestrict_ker_finrank [FiniteDimensional 𝕜 H] (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.ker N.dualRestrict) = finrank 𝕜 (H ⧸ N) := by
  rw [N.dualRestrict_ker_eq_dualAnnihilator]
  exact (Subspace.quotEquivAnnihilator N).finrank_eq.symm

theorem rank_restrict_add_codim [FiniteDimensional 𝕜 H]
    (F : H →ₗ[𝕜] Module.Dual 𝕜 H) (N : Submodule 𝕜 H) :
    finrank 𝕜 (LinearMap.range F) ≤
      finrank 𝕜 (LinearMap.range (restrictForm F N)) + 2 * finrank 𝕜 (H ⧸ N) := by
  have hdomain := rank_domRestrict_add_codim F N
  have hcodomain := rank_le_rank_comp_add_ker (F.domRestrict N) N.dualRestrict
  rw [dualRestrict_ker_finrank] at hcodomain
  change finrank 𝕜 (LinearMap.range (F.domRestrict N)) ≤
    finrank 𝕜 (LinearMap.range (restrictForm F N)) + finrank 𝕜 (H ⧸ N) at hcodomain
  omega

end
end PerfectCompleteness.BilinearRestrictionRank

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_RecursiveSpaceEquivLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.SmallBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Foundations.Information

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem expectation_mono (μ : FiniteDistribution Ω) {a b : Ω → ℝ}
    (h : ∀ x, a x ≤ b x) : μ.expectation a ≤ μ.expectation b := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

end

end PerfectCompleteness.SmallBias

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_UniformLinearImage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

end
end PerfectCompleteness.UniformLinearImage

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Games_FinishBoundsLemmas
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatent
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.UniformLatent

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open FiniteProduct CleanConditioning

noncomputable section

theorem probability_uniform_singleton {A : Type*} [Fintype A] [Nonempty A]
    [DecidableEq A] (a : A) :
    (FiniteDistribution.uniform A).probability (fun x => decide (x = a)) =
      1 / (Fintype.card A : ℝ) := by
  simp [FiniteDistribution.probability, FiniteDistribution.uniform]


end
end PerfectCompleteness.UniformLatent

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_AffineFunctionalDependence
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveEquiv_val _root_.OAI.UniqueGamesTheorem.Appendix.A13Index.positiveMap_val _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.forget_val _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.base_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_apply _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.compress_lift _root_.OAI.UniqueGamesTheorem.Appendix.CompressionCount.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.complementParameter_val _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.coordinateEquiv_apply _root_.OAI.UniqueGamesTheorem.Appendix.DerivativeInduction.lift_apply _root_.OAI.UniqueGamesTheorem.Appendix.FullCompression.compression_apply _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight _root_.OAI.UniqueGamesTheorem.Fourier.MatrixNoise.dotCharacter_apply _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_firstBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_hBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualHomogeneous.tau_secondBasis _root_.OAI.UniqueGamesTheorem.Reduction.ActualSource.alphabetEmbedding_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.AffineFunctionalDependence

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

noncomputable section

private theorem probability_cover_le_sum {Ω I : Type*} [Fintype Ω] [Fintype I]
    (μ : FiniteDistribution Ω) (event : Ω → Bool) (cover : I → Ω → Bool)
    (hcover : ∀ x, event x = true → ∃ i, cover i x = true) :
    μ.probability event ≤ ∑ i, μ.probability (cover i) := by
  unfold FiniteDistribution.probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : event x = true
  · obtain ⟨i, hi⟩ := hcover x hx
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun j => if cover j x then μ.weight x else 0) (a := i)
      (fun j _ => by split <;> first | exact μ.nonnegative x | exact le_rfl)
      (Finset.mem_univ i)
    simpa only [hx, hi, ite_true, if_true] using h
  · simp only [hx]
    apply Finset.sum_nonneg
    intro i _
    split
    · exact μ.nonnegative x
    · exact le_rfl

variable {N V : Type*} [AddCommGroup N] [Module F2 N]
  [AddCommGroup V] [Module F2 V] [Fintype N] [Fintype V]

theorem affine_zero_probability_le (f : N →ₗ[F2] V) (b : V) :
    (FiniteDistribution.uniform N).probability (fun x => decide (b + f x = 0)) ≤
      1 / (Fintype.card (LinearMap.range f) : ℝ) := by
  have hlaw := UniformLinearImage.uniform_pushforward_linearMap
    f.rangeRestrict f.surjective_rangeRestrict
  have hp := congrArg (fun μ : FiniteDistribution (LinearMap.range f) =>
    μ.probability (fun y => decide (b + (y : V) = 0))) hlaw
  rw [FiniteDistribution.probability_pushforward] at hp
  change (FiniteDistribution.uniform N).probability
    (fun x => decide (b + f x = 0)) = _ at hp
  rw [hp]
  by_cases hzero : ∃ y : LinearMap.range f, b + (y : V) = 0
  · obtain ⟨z, hz⟩ := hzero
    have hevent : (fun y : LinearMap.range f => decide (b + (y : V) = 0)) =
        (fun y => decide (y = z)) := by
      funext y
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      constructor
      · intro hy
        apply Subtype.ext
        exact add_left_cancel (hy.trans hz.symm)
      · rintro rfl
        exact hz
    rw [hevent, UniformLatent.probability_uniform_singleton]
  · have hz : ∀ y : LinearMap.range f, b + (y : V) ≠ 0 := by
      simpa only [not_exists] using hzero
    simp [FiniteDistribution.probability, hz]

variable {m : Nat}

theorem coefficientSum_surjective (c : Fin m → F2) (hc : c ≠ 0) :
    Function.Surjective (coefficientSum (N := N) c) := by
  have hcoord : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨i, hi⟩ := hcoord
  have hi1 : c i = 1 :=
    (UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (c i)).resolve_left hi
  intro n
  refine ⟨Function.update 0 i n, ?_⟩
  rw [coefficientSum_apply, Finset.sum_eq_single i]
  · simp [hi1]
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · intro h
    exact (h (Finset.mem_univ i)).elim

theorem relation_probability_le (f : N →ₗ[F2] V) (offsets : Fin m → V)
    (c : Fin m → F2) (hc : c ≠ 0) :
    (FiniteDistribution.uniform (Fin m → N)).probability
        (fun x => decide ((∑ i, c i • (offsets i + f (x i))) = 0)) ≤
      1 / (Fintype.card (LinearMap.range f) : ℝ) := by
  have hlaw := UniformLinearImage.uniform_pushforward_linearMap
    (coefficientSum (N := N) c) (coefficientSum_surjective c hc)
  have hp := congrArg (fun μ : FiniteDistribution N =>
    μ.probability (fun n => decide ((∑ i, c i • offsets i) + f n = 0))) hlaw
  rw [FiniteDistribution.probability_pushforward] at hp
  have hevent :
      (fun x : Fin m → N => decide ((∑ i, c i • (offsets i + f (x i))) = 0)) =
      (fun x => decide ((∑ i, c i • offsets i) + f (coefficientSum c x) = 0)) := by
    funext x
    simp only [coefficientSum_apply, smul_add, Finset.sum_add_distrib,
      map_sum, map_smul]
  rw [hevent, hp]
  exact affine_zero_probability_le f (∑ i, c i • offsets i)

theorem dependence_probability_le (f : N →ₗ[F2] V) (offsets : Fin m → V) :
    (FiniteDistribution.uniform (Fin m → N)).probability
        (fun x => decide (¬ LinearIndependent F2 (fun i => offsets i + f (x i)))) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ Module.finrank F2 (LinearMap.range f) := by
  let μ := FiniteDistribution.uniform (Fin m → N)
  let event := fun x : Fin m → N =>
    decide (¬ LinearIndependent F2 (fun i => offsets i + f (x i)))
  let cover := fun (c : Fin m → F2) (x : Fin m → N) =>
    decide (c ≠ 0 ∧ (∑ i, c i • (offsets i + f (x i))) = 0)
  have hcover : ∀ x, event x = true → ∃ c, cover c x = true := by
    intro x hx
    have hdep : ¬ LinearIndependent F2 (fun i => offsets i + f (x i)) :=
      of_decide_eq_true hx
    obtain ⟨c, hc, i, hi⟩ := Fintype.not_linearIndependent_iff.mp hdep
    have hc0 : c ≠ 0 := by
      intro hz
      exact hi (congrFun hz i)
    refine ⟨c, ?_⟩
    exact decide_eq_true_eq.mpr ⟨hc0, hc⟩
  have hbound (c : Fin m → F2) :
      μ.probability (cover c) ≤ 1 / (Fintype.card (LinearMap.range f) : ℝ) := by
    by_cases hc : c = 0
    · subst c
      simp [cover, FiniteDistribution.probability]
    · simpa [μ, cover, hc] using relation_probability_le f offsets c hc
  calc
    μ.probability event ≤ ∑ c, μ.probability (cover c) :=
      probability_cover_le_sum μ event cover hcover
    _ ≤ ∑ _c : Fin m → F2, 1 / (Fintype.card (LinearMap.range f) : ℝ) :=
      Finset.sum_le_sum (fun c _ => hbound c)
    _ = (2 : ℝ) ^ m / (2 : ℝ) ^ Module.finrank F2 (LinearMap.range f) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin,
        Module.card_eq_pow_finrank (K := F2) (V := LinearMap.range f),
        show Fintype.card F2 = 2 by decide, Nat.cast_pow, Nat.cast_ofNat,
        mul_one_div]

end
end PerfectCompleteness.AffineFunctionalDependence

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_BinaryRankOneCount
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.BinaryRankOneCount

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem rank_le_one_iff_vecMulVec {K I J : Type*} [Field K]
    [Fintype I] [Fintype J] (A : Matrix I J K) :
    A.rank ≤ 1 ↔ ∃ u : I → K, ∃ v : J → K, Matrix.vecMulVec u v = A := by
  constructor
  · intro hA
    let S : Submodule K (I → K) := Submodule.span K (Set.range A.col)
    have hS : Module.finrank K S ≤ 1 := by
      simpa only [S, Matrix.rank_eq_finrank_span_cols] using hA
    obtain ⟨u, hu⟩ := (finrank_le_one_iff (K := K) (V := S)).mp hS
    have hcol (j : J) : A.col j ∈ S :=
      Submodule.subset_span (Set.mem_range_self j)
    choose v hv using (fun j : J => hu ⟨A.col j, hcol j⟩)
    refine ⟨u.val, v, ?_⟩
    ext i j
    change u.val i * v j = A i j
    have hij := congrArg (fun z : S => z.val i) (hv j)
    change v j * u.val i = A i j at hij
    exact (mul_comm _ _).trans hij
  · rintro ⟨u, v, rfl⟩
    exact Matrix.rank_vecMulVec_le u v

theorem binary_rank_le_one_card_le (m : Nat) :
    Fintype.card {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.rank ≤ 1} ≤
      2 ^ (2 * m) := by
  let outer : ((Fin m → ZMod 2) × (Fin m → ZMod 2)) →
      {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.rank ≤ 1} :=
    fun p => ⟨Matrix.vecMulVec p.1 p.2, Matrix.rank_vecMulVec_le p.1 p.2⟩
  have covers : Function.Surjective outer := by
    intro A
    obtain ⟨u, v, huv⟩ := (rank_le_one_iff_vecMulVec A.val).mp A.property
    exact ⟨(u, v), Subtype.ext huv⟩
  have vector_card : Fintype.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]
  calc
    _ ≤ Fintype.card ((Fin m → ZMod 2) × (Fin m → ZMod 2)) :=
      Fintype.card_le_of_surjective outer covers
    _ = 2 ^ m * 2 ^ m := by rw [Fintype.card_prod, vector_card]
    _ = 2 ^ (2 * m) := by rw [← pow_add, two_mul]

theorem binary_matrix_card (m : Nat) :
    Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) = 2 ^ (m * m) := by
  change Fintype.card (Fin m → Fin m → ZMod 2) = _
  simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card, pow_mul]

theorem uniform_rank_le_one_probability_le (m : Nat) :
    (FiniteDistribution.uniform (Matrix (Fin m) (Fin m) (ZMod 2))).probability
        (fun A => decide (A.rank ≤ 1)) ≤
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  have hcount :
      (Fintype.card {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.rank ≤ 1} : ℝ) ≤
        (2 : ℝ) ^ (2 * m) := by
    exact_mod_cast binary_rank_le_one_card_le m
  calc
    _ = (∑ A : Matrix (Fin m) (Fin m) (ZMod 2),
          if A.rank ≤ 1 then (1 : ℝ) else 0) /
        (Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) : ℝ) := by
      change (∑ A : Matrix (Fin m) (Fin m) (ZMod 2),
        if decide (A.rank ≤ 1) then
          1 / (Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) : ℝ) else 0) = _
      simp only [div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro A _
      by_cases hA : A.rank ≤ 1 <;> simp [hA]
    _ = (Fintype.card {A : Matrix (Fin m) (Fin m) (ZMod 2) // A.rank ≤ 1} : ℝ) /
        (Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) : ℝ) := by
      simp only [Fintype.card_subtype, Finset.sum_boole]
    _ ≤ (2 : ℝ) ^ (2 * m) /
        (Fintype.card (Matrix (Fin m) (Fin m) (ZMod 2)) : ℝ) :=
      div_le_div_of_nonneg_right hcount (Nat.cast_nonneg _)
    _ = (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
      rw [binary_matrix_card]
      norm_cast

end
end PerfectCompleteness.BinaryRankOneCount

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_LowerCrossRank
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.GoodRowSampling.rowFiberEquiv_val _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OutputAnnihilator.mem_bad _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_fst _root_.OAI.PerfectCompleteness.RestrictionCrossLaw.selectedPair_snd _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_apply _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.rowsLinear_fromRows _root_.OAI.PerfectCompleteness.RestrictionRowsLaw.selectedRowsLinear_apply _root_.OAI.PerfectCompleteness.TensorProjectedSlice.totalMatrix_apply _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.LowerCrossRank

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

section Evaluation

variable {K I N : Type*} [Field K] [Fintype I]
  [AddCommGroup N] [Module K N]

theorem evaluation_surjective (forms : I → Module.Dual K N)
    (hforms : LinearIndependent K forms) : Function.Surjective (LinearMap.pi forms) := by
  have hfun : LinearIndependent K (fun i => (forms i : N → K)) := by
    exact hforms.map' (LinearMap.ltoFun K N K K)
      (LinearMap.ker_eq_bot.mpr DFunLike.coe_injective)
  have hspan : Submodule.span K
      (Set.range (fun n : N => fun i : I => forms i n)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr hfun
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨n, rfl⟩
  exact ⟨n, rfl⟩

variable {J : Type*} [Fintype J]

omit [Fintype J] in
theorem crossLinear_surjective (forms : I → Module.Dual K N)
    (hforms : LinearIndependent K forms) :
    Function.Surjective (crossLinear (J := J) forms) := by
  intro M
  have h := evaluation_surjective forms hforms
  choose y hy using (fun j : J => h (fun i => M i j))
  refine ⟨y, ?_⟩
  ext i j
  exact congrFun (hy j) i

end Evaluation

private theorem uniform_pushforward_perm {A : Type*} [Fintype A] [Nonempty A]
    (e : A ≃ A) :
    (FiniteDistribution.uniform A).pushforward e = FiniteDistribution.uniform A := by
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∑ x : A, if e x = y then (1 / (Fintype.card A : ℝ)) else 0) =
    1 / (Fintype.card A : ℝ)
  simp_rw [← e.eq_symm_apply]
  simp

section UniformCross

variable {I J N : Type*} [Fintype I] [Fintype J]
  [AddCommGroup N] [Module F2 N] [Fintype N]
  [Fintype (J → N)] [Fintype (Matrix I J F2)]

omit [Fintype N] [Fintype J] in
theorem affine_cross_uniform (forms : I → Module.Dual F2 N)
    (hforms : LinearIndependent F2 forms) (offset : Matrix I J F2) :
    (FiniteDistribution.uniform (J → N)).pushforward (Γ := Matrix I J F2)
        (fun y i j => offset i j + forms i (y j)) =
      FiniteDistribution.uniform (Matrix I J F2) := by
  calc
    _ = ((FiniteDistribution.uniform (J → N)).pushforward (Γ := Matrix I J F2)
        (crossLinear forms)).pushforward (Γ := Matrix I J F2)
        (fun M => offset + M) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = (FiniteDistribution.uniform (Matrix I J F2)).pushforward (Γ := Matrix I J F2)
        (fun M => offset + M) := by
      rw [UniformLinearImage.uniform_pushforward_linearMap
        (crossLinear forms) (crossLinear_surjective forms hforms)]
    _ = _ := uniform_pushforward_perm (Equiv.addLeft offset)

end UniformCross


variable {H : Type*} [AddCommGroup H] [Module F2 H]
  [Fintype H] [FiniteDimensional F2 H]
  (F : H →ₗ[F2] Module.Dual F2 H) (N : Submodule F2 H)
  {m : Nat} (u v : Fin m → H)

omit [FiniteDimensional F2 H] in
theorem crossMatrix_uniform_of_independent (x : Fin m → N)
    (hx : LinearIndependent F2 (firstFunctionals F N u x)) :
    (FiniteDistribution.uniform (Fin m → N)).pushforward
        (crossMatrix F N u v x) =
      FiniteDistribution.uniform (Matrix (Fin m) (Fin m) F2) := by
  have h := affine_cross_uniform (firstFunctionals F N u x) hx
    (fun i j => F (u i + (x i : H)) (v j))
  have heq : crossMatrix F N u v x =
      fun y i j => F (u i + (x i : H)) (v j) +
        firstFunctionals F N u x i (y j) := by
    funext y i j
    exact map_add (F (u i + (x i : H))) (v j) (y j : H)
  rw [heq]
  exact h

omit [FiniteDimensional F2 H] in
theorem conditional_rank_probability_le (x : Fin m → N)
    (hx : LinearIndependent F2 (firstFunctionals F N u x)) :
    (FiniteDistribution.uniform (Fin m → N)).probability
        (fun y => decide ((crossMatrix F N u v x y).rank ≤ 1)) ≤
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  have h := congrArg (fun μ : FiniteDistribution (Matrix (Fin m) (Fin m) F2) =>
    μ.probability (fun M => decide (M.rank ≤ 1)))
    (crossMatrix_uniform_of_independent F N u v x hx)
  rw [FiniteDistribution.probability_pushforward] at h
  rw [h]
  exact BinaryRankOneCount.uniform_rank_le_one_probability_le m

private theorem probability_product {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteDistribution A) (ν : FiniteDistribution B) (event : A × B → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun a => ν.probability (fun b => event (a, b))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    FiniteDistribution.product, Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

omit [FiniteDimensional F2 H] in
theorem cross_rank_probability_le :
    ((FiniteDistribution.uniform (Fin m → N)).product
        (FiniteDistribution.uniform (Fin m → N))).probability
        (fun p => decide ((crossMatrix F N u v p.1 p.2).rank ≤ 1)) ≤
      (2 : ℝ) ^ m /
        (2 : ℝ) ^ Module.finrank F2
          (LinearMap.range (BilinearRestrictionRank.restrictForm F N)) +
      (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  let : Fintype (Module.Dual F2 N) :=
    Fintype.ofInjective (fun f : Module.Dual F2 N => (f : N → F2))
      DFunLike.coe_injective
  let q : ℝ := (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m)
  have hq : 0 ≤ q := by positivity
  have hdep := AffineFunctionalDependence.dependence_probability_le
    (BilinearRestrictionRank.restrictForm F N)
    (fun i => N.dualRestrict (F (u i)))
  have hforms (x : Fin m → N) : firstFunctionals F N u x =
      fun i => N.dualRestrict (F (u i)) +
        BilinearRestrictionRank.restrictForm F N (x i) := by
    funext i
    simp [firstFunctionals, BilinearRestrictionRank.restrictForm, map_add]
  have hdep' : (FiniteDistribution.uniform (Fin m → N)).probability
      (fun x => decide (¬ LinearIndependent F2 (firstFunctionals F N u x))) ≤
        (2 : ℝ) ^ m /
          (2 : ℝ) ^ Module.finrank F2
            (LinearMap.range (BilinearRestrictionRank.restrictForm F N)) := by
    simpa only [hforms] using hdep
  rw [probability_product]
  calc
    _ ≤ (FiniteDistribution.uniform (Fin m → N)).expectation
        (fun x => (if ¬ LinearIndependent F2 (firstFunctionals F N u x)
          then (1 : ℝ) else 0) + q) := by
      apply SmallBias.expectation_mono
      intro x
      by_cases hx : LinearIndependent F2 (firstFunctionals F N u x)
      · simpa only [hx, not_true_eq_false, ite_false, if_false, zero_add] using
          conditional_rank_probability_le F N u v x hx
      · simpa only [hx, not_false_eq_true, ite_true, if_true] using
          ((FiniteDistribution.uniform (Fin m → N)).probability_le_one
            (fun y => decide ((crossMatrix F N u v x y).rank ≤ 1))).trans
            (le_add_of_nonneg_right hq)
    _ = (FiniteDistribution.uniform (Fin m → N)).probability
        (fun x => decide (¬ LinearIndependent F2 (firstFunctionals F N u x))) + q := by
      simp [FiniteDistribution.expectation, FiniteDistribution.probability,
        mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib,
        ← Finset.sum_mul, FiniteDistribution.normalized, one_mul]
    _ ≤ _ := add_le_add hdep' (le_refl q)

theorem cross_rank_probability_le_of_rank_gt (r s : Nat)
    (hcodim : Module.finrank F2 (H ⧸ N) ≤ r)
    (hrank : s < Module.finrank F2 (LinearMap.range F)) :
    ((FiniteDistribution.uniform (Fin m → N)).product
        (FiniteDistribution.uniform (Fin m → N))).probability
        (fun p => decide ((crossMatrix F N u v p.1 p.2).rank ≤ 1)) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
        (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  have hloss := BilinearRestrictionRank.rank_restrict_add_codim F N
  have hexp : s - 2 * r ≤ Module.finrank F2
      (LinearMap.range (BilinearRestrictionRank.restrictForm F N)) := by omega
  apply (cross_rank_probability_le F N u v).trans
  apply add_le_add _ (le_refl _)
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (pow_le_pow_right₀ (by norm_num) hexp)

end
end PerfectCompleteness.LowerCrossRank

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DualQuotientRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DualQuotientRows

noncomputable section

open Module
open UniqueGamesTheorem.Foundations.Games

variable {𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

theorem codim_dualAnnihilator_eq [FiniteDimensional 𝕜 E] (W : Submodule 𝕜 E) :
    finrank 𝕜 (Module.Dual 𝕜 E ⧸ W.dualAnnihilator) = finrank 𝕜 W := by
  have hquotient := W.dualAnnihilator.finrank_quotient_add_finrank
  have hannihilator := Subspace.finrank_add_finrank_dualAnnihilator_eq W
  rw [Subspace.dual_finrank_eq] at hquotient
  omega

end
end PerfectCompleteness.DualQuotientRows



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RestrictionRowsLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RestrictionRowsLaw

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Foundations.Games
open scoped Classical

variable {E C I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [Fintype I]
  (W : Submodule F2 E) (C' : Submodule F2 C) (b : Module.Basis I F2 C')

theorem rowsLinear_surjective : Function.Surjective (rowsLinear W C' b) :=
  fun rows => ⟨fromRows W C' b rows, rowsLinear_fromRows W C' b rows⟩

section Selection

variable {J : Type*} (sel : J → I)

omit [Fintype I] in
theorem selectLinear_surjective (hsel : Function.Injective sel) :
    Function.Surjective (selectLinear W sel) :=
  hsel.surjective_comp_right

theorem selectedRowsLinear_surjective (hsel : Function.Injective sel) :
    Function.Surjective (selectedRowsLinear W C' b sel) :=
  (selectLinear_surjective W sel hsel).comp (rowsLinear_surjective W C' b)

end Selection

omit [Fintype I] in
theorem coordinate_translate (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C) (A : Parameter W C') (i : I) :
    (coordinates i).comp (translate W C' X A) =
      affineRow W ((coordinates i).comp X) (rowsLinear W C' b A i) := by
  apply LinearMap.ext
  intro x
  change coordinates i (X x + (A (W.mkQ x) : C)) =
    coordinates i (X x) + b.coord i (A (W.mkQ x))
  rw [map_add]
  congr 1
  exact congrArg (fun f : C' →ₗ[F2] F2 => f (A (W.mkQ x))) (hcoordinates i)


end
end PerfectCompleteness.RestrictionRowsLaw

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RestrictionCrossLaw
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RestrictionCrossLaw

noncomputable section

open UniqueGamesTheorem.Integration.BinaryLinear (F2)
open UniqueGamesTheorem.Fourier.MatrixRestrictions
open UniqueGamesTheorem.Foundations.Games
open RestrictionRowsLaw DualQuotientRows

variable {E C I : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup C] [Module F2 C] [Fintype I]
  (W : Submodule F2 E) (C' : Submodule F2 C) (b : Module.Basis I F2 C')

variable {m : Nat} (sel : (Fin m ⊕ Fin m) → I)

theorem selectedPair_surjective (hsel : Function.Injective sel) :
    Function.Surjective (selectedPair W C' b sel) :=
  (rowPairEquiv W m).surjective.comp (selectedRowsLinear_surjective W C' b sel hsel)

private theorem uniform_product {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] :
    (FiniteDistribution.uniform A).product (FiniteDistribution.uniform B) =
      FiniteDistribution.uniform (A × B) := by
  apply FiniteDistribution.eq_of_weight_eq
  intro p
  change (1 / (Fintype.card A : ℝ)) * (1 / (Fintype.card B : ℝ)) =
    1 / (Fintype.card (A × B) : ℝ)
  simp only [Fintype.card_prod, Nat.cast_mul, one_div, mul_inv]

theorem selectedPair_law [Fintype (Parameter W C')] [Fintype W.dualAnnihilator]
    (hsel : Function.Injective sel) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward (selectedPair W C' b sel) =
      (FiniteDistribution.uniform (Fin m → W.dualAnnihilator)).product
        (FiniteDistribution.uniform (Fin m → W.dualAnnihilator)) := by
  rw [uniform_product]
  exact UniformLinearImage.uniform_pushforward_linearMap
    (selectedPair W C' b sel) (selectedPair_surjective W C' b sel hsel)

omit [Fintype I] in
theorem coordinate_translate_left (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C) (A : Parameter W C') (i : Fin m) :
    (coordinates (sel (Sum.inl i))).comp (translate W C' X A) =
      (coordinates (sel (Sum.inl i))).comp X +
        ((selectedPair W C' b sel A).1 i : Module.Dual F2 E) := by
  simpa only [affineRow, selectedPair_fst, quotientRowEquiv_val] using
    coordinate_translate W C' b coordinates hcoordinates X A (sel (Sum.inl i))

omit [Fintype I] in
theorem coordinate_translate_right (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C) (A : Parameter W C') (j : Fin m) :
    (coordinates (sel (Sum.inr j))).comp (translate W C' X A) =
      (coordinates (sel (Sum.inr j))).comp X +
        ((selectedPair W C' b sel A).2 j : Module.Dual F2 E) := by
  simpa only [affineRow, selectedPair_snd, quotientRowEquiv_val] using
    coordinate_translate W C' b coordinates hcoordinates X A (sel (Sum.inr j))

theorem crossMatrix_law [Fintype (Parameter W C')] [Fintype W.dualAnnihilator]
    (hsel : Function.Injective sel)
    (coordinates : I → Module.Dual F2 C)
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] C)
    (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E)) :
    (FiniteDistribution.uniform (Parameter W C')).pushforward
        (Γ := Matrix (Fin m) (Fin m) F2)
        (fun A i j =>
          F ((coordinates (sel (Sum.inl i))).comp (translate W C' X A))
            ((coordinates (sel (Sum.inr j))).comp (translate W C' X A))) =
      ((FiniteDistribution.uniform (Fin m → W.dualAnnihilator)).product
        (FiniteDistribution.uniform (Fin m → W.dualAnnihilator))).pushforward
          (Γ := Matrix (Fin m) (Fin m) F2)
          (fun p => LowerCrossRank.crossMatrix F W.dualAnnihilator
            (fun i => (coordinates (sel (Sum.inl i))).comp X)
            (fun j => (coordinates (sel (Sum.inr j))).comp X) p.1 p.2) := by
  have hcross :
      (fun (A : Parameter W C') =>
        (fun i j => F ((coordinates (sel (Sum.inl i))).comp (translate W C' X A))
          ((coordinates (sel (Sum.inr j))).comp (translate W C' X A)) :
            Matrix (Fin m) (Fin m) F2)) =
      (fun A => LowerCrossRank.crossMatrix F W.dualAnnihilator
        (fun i => (coordinates (sel (Sum.inl i))).comp X)
        (fun j => (coordinates (sel (Sum.inr j))).comp X)
        (selectedPair W C' b sel A).1 (selectedPair W C' b sel A).2) := by
    funext A i j
    rw [coordinate_translate_left W C' b sel coordinates hcoordinates X A i,
      coordinate_translate_right W C' b sel coordinates hcoordinates X A j]
    rfl
  rw [hcross, ← FiniteDistribution.pushforward_comp
    (FiniteDistribution.uniform (Parameter W C')) (selectedPair W C' b sel)
    (fun p => LowerCrossRank.crossMatrix F W.dualAnnihilator
      (fun i => (coordinates (sel (Sum.inl i))).comp X)
      (fun j => (coordinates (sel (Sum.inr j))).comp X) p.1 p.2),
    selectedPair_law W C' b sel hsel]

end
end PerfectCompleteness.RestrictionCrossLaw

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_LowerAffineSliceRank
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype
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

omit [Fintype E] [FiniteDimensional F2 E] [Fintype (Module.Dual F2 E)] in
theorem coordinate_eq_sum (X : E →ₗ[F2] (Fin ℓ → F2))
    (q : Module.Dual F2 (Fin ℓ → F2)) :
    q.comp X = ∑ k, q (Pi.single k 1) • matrixRows X k := by
  apply LinearMap.ext
  intro e
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    matrixRows, LinearMap.proj_apply, smul_eq_mul]
  change q (X e) = ∑ k, q (Pi.single k 1) * X e k
  have hrows := pi_eq_sum_univ' (X e)
  calc
    q (X e) = q (∑ k : Fin ℓ, (X e k) • Pi.single k (1 : F2)) :=
      congrArg q hrows
    _ = ∑ k : Fin ℓ, (X e k) * q (Pi.single k 1) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = _ := Finset.sum_congr rfl (fun k _ => mul_comm _ _)

omit [Fintype E] [FiniteDimensional F2 E] [Fintype (Module.Dual F2 E)] in
theorem coordinate_cross_rank_le
    (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))
    (X : E →ₗ[F2] (Fin ℓ → F2))
    (left right : Fin m → Module.Dual F2 (Fin ℓ → F2)) :
    Matrix.rank ((fun i j => F ((left i).comp X) ((right j).comp X)) :
      Matrix (Fin m) (Fin m) F2) ≤
      (testedGram F X).rank := by
  have hleft : combinations (matrixRows X)
      (fun i k => left i (Pi.single k 1)) = fun i => (left i).comp X := by
    funext i
    exact (coordinate_eq_sum X (left i)).symm
  have hright : combinations (matrixRows X)
      (fun j k => right j (Pi.single k 1)) = fun j => (right j).comp X := by
    funext j
    exact (coordinate_eq_sum X (right j)).symm
  have h := cross_rank_le F (matrixRows X)
    (fun i k => left i (Pi.single k 1))
    (fun j k => right j (Pi.single k 1))
  rw [hleft, hright] at h
  exact h

section Coordinates

variable {I : Type*} [Fintype I]
  (W : Submodule F2 E) (C' : Submodule F2 (Fin ℓ → F2))
  (b : Module.Basis I F2 C') (sel : (Fin m ⊕ Fin m) → I)

theorem slice_probability_le_of_coordinates_oai (hsel : Function.Injective sel)
    (coordinates : I → Module.Dual F2 (Fin ℓ → F2))
    (hcoordinates : ∀ i, (coordinates i).comp C'.subtype = b.coord i)
    (X : E →ₗ[F2] (Fin ℓ → F2))
    (F : Module.Dual F2 E →ₗ[F2] Module.Dual F2 (Module.Dual F2 E))
    (r s : Nat) (hW : Module.finrank F2 W ≤ r)
    (hrank : s < Module.finrank F2 (LinearMap.range F)) :
    (FiniteDistribution.uniform (Parameter W C')).probability
        (fun A => decide ((testedGram F (translate W C' X A)).rank ≤ 1)) ≤
      (2 : ℝ) ^ m / (2 : ℝ) ^ (s - 2 * r) +
        (2 : ℝ) ^ (2 * m) / (2 : ℝ) ^ (m * m) := by
  have hlaw := RestrictionCrossLaw.crossMatrix_law W C' b sel hsel
    coordinates hcoordinates X F
  have hp := congrArg
    (fun μ : FiniteDistribution (Matrix (Fin m) (Fin m) F2) =>
      μ.probability (fun M => decide (M.rank ≤ 1))) hlaw
  simp only [FiniteDistribution.probability_pushforward] at hp
  have hsource := FiniteDistribution.probability_pushforward
    (Γ := Matrix (Fin m) (Fin m) F2)
    (FiniteDistribution.uniform (Parameter W C'))
    (fun A i j =>
      F ((coordinates (sel (Sum.inl i))).comp (translate W C' X A))
        ((coordinates (sel (Sum.inr j))).comp (translate W C' X A)))
    (fun M => decide (M.rank ≤ 1))
  have hp' := hsource.symm.trans hp
  have hcodim : Module.finrank F2
      (Module.Dual F2 E ⧸ W.dualAnnihilator) ≤ r := by
    rw [DualQuotientRows.codim_dualAnnihilator_eq]
    exact hW
  calc
    _ ≤ (FiniteDistribution.uniform (Parameter W C')).probability
        (fun A => decide (Matrix.rank ((fun i j =>
          F ((coordinates (sel (Sum.inl i))).comp (translate W C' X A))
            ((coordinates (sel (Sum.inr j))).comp (translate W C' X A))) :
              Matrix (Fin m) (Fin m) F2) ≤ 1)) := by
      apply FiniteDistribution.probability_mono
      intro A hA
      apply decide_eq_true
      exact (coordinate_cross_rank_le F (translate W C' X A)
        (fun i => coordinates (sel (Sum.inl i)))
        (fun j => coordinates (sel (Sum.inr j)))).trans (of_decide_eq_true hA)
    _ = _ := hp'
    _ ≤ _ := LowerCrossRank.cross_rank_probability_le_of_rank_gt F W.dualAnnihilator
      (fun i => (coordinates (sel (Sum.inl i))).comp X)
      (fun j => (coordinates (sel (Sum.inr j))).comp X) r s hcodim hrank

end Coordinates


end
end PerfectCompleteness.LowerAffineSliceRank

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PerfectCompleteness.LowerAffineSliceRank.slice_probability_le_of_coordinates_oai.{u_1, u_2} := @OAI.PerfectCompleteness.LowerAffineSliceRank.slice_probability_le_of_coordinates_oai.{u_1, u_2}
