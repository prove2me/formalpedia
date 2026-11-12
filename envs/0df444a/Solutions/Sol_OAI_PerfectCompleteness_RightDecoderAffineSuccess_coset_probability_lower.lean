-- Prove2me | solution 1 for OAI.PerfectCompleteness.RightDecoderAffineSuccess.coset_probability_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:15:52.045424+00:00
-- url     : https://prove2.me/submissions/771fea64-a4d0-473b-ad3c-24d18549f5e7

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
import Theorems.Thm_OAI_PerfectCompleteness_OwnInputHeavyBounds_heavyList_card_le_of_balanced
import Theorems.Thm_OAI_PerfectCompleteness_TensorAffineHeavyWitness_exists_heavy_candidate

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_DecoderContraction
attribute [-instance] _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DecoderContraction

open scoped TensorProduct Classical
open TensorCosetEvaluation
open PointwiseSpaces RecursiveSpaces

noncomputable section

variable {K H : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H]

theorem chosenRow_value_one (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (hσ : σ.comp W.subtype ≠ 0) : σ (chosenRow W σ hσ).val = 1 :=
  Classical.choose_spec (exists_value_one (σ.comp W.subtype) hσ)

theorem contract_eq (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hσ : σ.comp W.subtype ≠ 0) :
    contract W σ Φ = scalarRestriction Φ (chosenRow W σ hσ) := by
  simp only [contract, dite_eq_left hσ]

theorem contract_baseFrequency (W : Submodule F2 K) (σ : Module.Dual F2 K)
    (z : Module.Dual F2 H) (hσ : σ.comp W.subtype ≠ 0) :
    contract W σ (baseFrequency W σ z) = z := by
  rw [contract_eq W σ _ hσ]
  change scalarRestriction (pureFrequency (σ.comp W.subtype) z) (chosenRow W σ hσ) = z
  rw [scalarRestriction_pure]
  change σ (chosenRow W σ hσ).val • z = z
  rw [chosenRow_value_one, one_smul]

theorem contract_sub_mem (W : Submodule F2 K) (Q : Submodule F2 (Module.Dual F2 H))
    (σ : Module.Dual F2 K) (Φ : Module.Dual F2 (W ⊗[F2] H)) (z : Module.Dual F2 H)
    (hσ : σ.comp W.subtype ≠ 0) (hΦ : Φ - baseFrequency W σ z ∈ errorSpace W Q) :
    contract W σ Φ - z ∈ Q := by
  have h := hΦ (chosenRow W σ hσ)
  rw [scalarRestriction_sub] at h
  rw [contract_eq W σ Φ hσ]
  have hbase : scalarRestriction (baseFrequency W σ z) (chosenRow W σ hσ) = z := by
    rw [← contract_eq W σ _ hσ]
    exact contract_baseFrequency W σ z hσ
  rw [hbase] at h
  exact h


end
end PerfectCompleteness.DecoderContraction

end OAI
end

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_KernelSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype _root_.OAI.UniqueGamesTheorem.Fourier.MatrixRestrictions.parameterFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.SmallBias.expectation_const _root_.OAI.PerfectCompleteness.SmallBias.expectation_neg _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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

theorem pushforward_comp (μ : FiniteDistribution A) (f : A → B) (g : B → C) :
    (μ.pushforward f).pushforward g = μ.pushforward (fun a => g (f a)) := by
  classical
  apply eq_of_weight_eq
  intro c
  rw [weight_eq_probability_singleton, weight_eq_probability_singleton]
  simp only [probability_pushforward]

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_FiniteProduct
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteProduct

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem expectation_product (P : (i : I) → FiniteDistribution (Ω i))
    (f : (i : I) → Ω i → ℝ) :
    (law P).expectation (fun x => ∏ i, f i (x i)) =
      ∏ i, (P i).expectation (f i) := by
  change (∑ x : (i : I) → Ω i, (∏ i, (P i).weight (x i)) *
      (∏ i, f i (x i))) = ∏ i, ∑ a, (P i).weight a * f i a
  simp only [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i a => (P i).weight a * f i a)).symm

omit [∀ index, Fintype (Ω index)] in
theorem product_factor (i : I) (f : Ω i → ℝ) (x : (j : I) → Ω j) :
    (∏ j, factor i f j (x j)) = f (x i) := by
  classical
  rw [Finset.prod_eq_single i]
  · exact factor_self i f (x i)
  · intro j _ h
    exact factor_other i j h f (x j)
  · simp

theorem expectation_factor_product (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) (f : Ω i → ℝ) :
    (∏ j, (P j).expectation (factor i f j)) = (P i).expectation f := by
  classical
  rw [Finset.prod_eq_single i]
  · congr 1
    funext a
    exact factor_self i f a
  · intro j _ h
    rw [factor_function_other i j h, SmallBias.expectation_const]
  · simp

theorem expectation_eval (P : (i : I) → FiniteDistribution (Ω i))
    (i : I) (f : Ω i → ℝ) :
    (law P).expectation (fun x => f (x i)) = (P i).expectation f := by
  calc
    _ = (law P).expectation (fun x => ∏ j, factor i f j (x j)) := by
      apply FiniteDistribution.expectation_congr
      intro x
      exact (product_factor i f x).symm
    _ = ∏ j, (P j).expectation (factor i f j) := expectation_product P _
    _ = _ := expectation_factor_product P i f

end
end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_QuarterBalanceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineLinearHeavyWitness.card_badMasks _root_.OAI.PerfectCompleteness.AffineLinearHeavyWitness.mem_badMasks _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.abs_character _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.bitSign_toBool _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.character_zero _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.frequency_apply_basis _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.ofBool_toBool _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.QuarterBalance

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness SmallBias

noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem bit_probabilities (μ : FiniteDistribution Ω) (f : Ω → F2) :
    μ.probability (fun x => decide (f x = 0)) +
      μ.probability (fun x => decide (f x = 1)) = 1 := by
  rw [← μ.normalized]
  simp only [FiniteDistribution.probability, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  have hb : f x = 0 ∨ f x = 1 := scalar_cases (f x)
  rcases hb with h | h <;> simp [h]

theorem expectation_sign (μ : FiniteDistribution Ω) (f : Ω → F2) :
    μ.expectation (fun x => sign (f x)) =
      2 * μ.probability (fun x => decide (f x = 0)) - 1 := by
  rw [← μ.normalized]
  simp only [FiniteDistribution.expectation, FiniteDistribution.probability,
    Finset.mul_sum, ← Finset.sum_sub_distrib, sign]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = 0 <;> simp [h]
  ring

theorem bias_of_balanced_bits (μ : FiniteDistribution Ω) (f : Ω → F2)
    (c : ℝ) (lower : ∀ b : F2, c ≤ μ.probability (fun x => decide (f x = b))) :
    |μ.expectation (fun x => sign (f x))| ≤ 1 - 2 * c := by
  rw [expectation_sign]
  have h0 := lower 0
  have h1 := lower 1
  have ht := bit_probabilities μ f
  exact abs_le.mpr ⟨by linarith, by linarith⟩

variable {V W : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]
  [AddCommGroup W] [Module F2 W] [Fintype W]

theorem balanced_of_bias_le_half (μ : FiniteDistribution V)
    (bias : ∀ f : V →ₗ[F2] F2, f ≠ 0 →
      |μ.expectation (fun x => sign (f x))| ≤ (1 / 2 : ℝ)) : Balanced μ := by
  intro f hf b
  have h := abs_le.mp (bias f hf)
  rw [expectation_sign] at h
  have ht := bit_probabilities μ f
  rcases scalar_cases b with rfl | rfl <;> linarith

theorem bilinear_bit_lower (μ : FiniteDistribution V) (ν : FiniteDistribution W)
    (hμ : Balanced μ) (hν : Balanced ν)
    (B : V →ₗ[F2] W →ₗ[F2] F2) (nonzero : B ≠ 0) (b : F2) :
    (1 / 16 : ℝ) ≤ (μ.product ν).probability (fun z => decide (B z.1 z.2 = b)) := by
  classical
  have hw : ∃ w : W, (B.flip w) ≠ 0 := by
    by_contra h
    push Not at h
    apply nonzero
    ext v w
    have he := congrArg (fun f : V →ₗ[F2] F2 => f v) (h w)
    simpa using he
  obtain ⟨w, hw⟩ := hw
  have lower (v : V) :
      (if B.flip w v = 1 then (1 / 4 : ℝ) else 0) ≤
        ν.probability (fun x => decide (B v x = b)) := by
    by_cases h : B.flip w v = 1
    · rw [ite_eq_left h]
      apply hν (B v)
      intro hz
      have he := congrArg (fun f : W →ₗ[F2] F2 => f w) hz
      have hh : B v w = 1 := h
      simp only [LinearMap.zero_apply] at he
      exact zero_ne_one (he.symm.trans hh)
    · rw [ite_eq_right h]
      exact ν.probability_nonnegative _
  have hfirst := hμ (B.flip w) hw 1
  calc
    (1 / 16 : ℝ) ≤ (1 / 4 : ℝ) * μ.probability (fun v => decide (B.flip w v = 1)) := by
      nlinarith
    _ = ∑ v, μ.weight v * (if B.flip w v = 1 then (1 / 4 : ℝ) else 0) := by
      simp only [FiniteDistribution.probability, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : B v w = 1 <;> simp [h, LinearMap.flip_apply]
      ring
    _ ≤ ∑ v, μ.weight v * ν.probability (fun x => decide (B v x = b)) :=
      Finset.sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (lower v) (μ.nonnegative v)
    _ = _ := by
      simp only [FiniteDistribution.probability, FiniteDistribution.product,
        Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro x _
      by_cases h : B v x = b <;> simp [h]

theorem bilinear_bias (μ : FiniteDistribution V) (ν : FiniteDistribution W)
    (hμ : Balanced μ) (hν : Balanced ν)
    (B : V →ₗ[F2] W →ₗ[F2] F2) (nonzero : B ≠ 0) :
    |(μ.product ν).expectation (fun z => sign (B z.1 z.2))| ≤ (7 / 8 : ℝ) := by
  have h := bias_of_balanced_bits (μ.product ν) (fun z => B z.1 z.2) (1 / 16)
    (bilinear_bit_lower μ ν hμ hν B nonzero)
  norm_num at h ⊢
  exact h

end
end PerfectCompleteness.QuarterBalance



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_UniformLinearImage
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.ClauseSupport.instNonemptyAnswer _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.ExpanderFamily.basePortNonempty _root_.OAI.UniqueGamesTheorem.Foundations.PCP.InitialGraph.vertexNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecursiveSamplerLaws
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.FiniteProduct

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω : I → Type*} [∀ i, Fintype (Ω i)]

theorem eval_pushforward (P : (i : I) → FiniteDistribution (Ω i)) (i : I) :
    (law P).pushforward (fun x => x i) = P i := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro a
  calc
    _ = (law P).expectation (fun x => if x i = a then 1 else 0) := by
      simp [FiniteDistribution.pushforward, FiniteDistribution.expectation, mul_ite]
    _ = (P i).expectation (fun b => if b = a then 1 else 0) :=
      expectation_eval P i (fun b => if b = a then (1 : ℝ) else 0)
    _ = _ := by simp [FiniteDistribution.expectation, mul_ite]

end
end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RecordSeedSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OddLists.OddList.instNonemptyOfNeZeroNat _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSampler

open PointwiseSpaces RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

variable (𝕜 : Type w) [Field 𝕜]

noncomputable section

variable [Finite 𝕜]

theorem tapeLaw_marginal (repeats : Nat → Nat) (p : Path branch n m)
    (A : Slots branch n → Type u) [∀ s, Finite (A s)] (j : DrawIndex repeats p) :
    (tapeLaw 𝕜 repeats p A).pushforward (fun t => t j) =
      FiniteDistribution.uniform (DrawSpace 𝕜 repeats p A j) :=
  FiniteProduct.eval_pushforward _ j

theorem law_refl_uniform (repeats : Nat → Nat) (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] [out : Fintype (space 𝕜 branch n A)] :
    law 𝕜 repeats (.refl n) A = FiniteDistribution.uniform (space 𝕜 branch n A) := by
  have hout : out = drawSpaceFintype 𝕜 repeats (.refl n) A () := Subsingleton.elim _ _
  cases hout
  exact tapeLaw_marginal 𝕜 repeats (.refl n) A ()

end
end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Construction_HiddenBucketBias
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketUniform.evaluateLinear_apply _root_.OAI.PerfectCompleteness.BucketUsefulCollision.fill_self _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_replace _root_.OAI.PerfectCompleteness.LowerDirectionFiber.complement_restore _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pairCoordinates_apply _root_.OAI.PerfectCompleteness.LowerDirectionFiber.pivot_value _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_complement _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_other _root_.OAI.PerfectCompleteness.LowerDirectionFiber.restore_pivot _root_.OAI.PerfectCompleteness.LowerDirectionFiber.split_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HiddenBucketBias

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators TensorProduct Classical

noncomputable section

variable {ℓ : Nat} {Ω H : Type*} [Fintype Ω]
  [AddCommGroup H] [Module F2 H]

theorem exists_nonzero_restriction (W : Submodule F2 (Fin ℓ → F2))
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    ∃ v : HiddenDirection W, scalarRestriction W Φ (directionIn W v) ≠ 0 := by
  by_contra hn
  apply hΦ
  apply TensorProduct.ext'
  intro v h
  by_cases hv : v = 0
  · simp [hv]
  · let d : HiddenDirection W :=
      ⟨⟨v.val, fun hzero => hv (Subtype.ext hzero)⟩, v.property⟩
    have hs : scalarRestriction W Φ (directionIn W d) = 0 := by
      by_contra hs
      exact hn ⟨d, hs⟩
    simpa only [scalarRestriction_apply, directionIn, d, LinearMap.zero_apply] using
      LinearMap.congr_fun hs h

theorem abs_character (χ : AddChar F2 ℝ) (b : F2) : |χ b| = 1 := by
  have hs : χ b * χ b = 1 := by
    rw [← χ.map_add_eq_mul, CharTwo.add_self_eq_zero, χ.map_zero_eq_one]
  have hs' : χ b ^ 2 = 1 := by simpa only [pow_two] using hs
  rcases sq_eq_one_iff.mp hs' with hb | hb <;> rw [hb] <;> norm_num

theorem character_sum {I : Type*} [Fintype I] (χ : AddChar F2 ℝ) (f : I → F2) :
    χ (∑ i, f i) = ∏ i, χ (f i) := by
  have h (s : Finset I) : χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi, χ.map_add_eq_mul, ih]
  exact h Finset.univ

omit [Fintype Ω] in
theorem character_hiddenSum (W : Submodule F2 (Fin ℓ → F2))
    (eval : Ω → H) (χ : AddChar F2 ℝ) (Φ : Module.Dual F2 (W ⊗[F2] H))
    (ω : HiddenTape W Ω) :
    χ (Φ (hiddenSum W eval ω)) =
      ∏ v : HiddenDirection W, χ (scalarRestriction W Φ (directionIn W v) (eval (ω v))) := by
  simp only [hiddenSum, map_sum, scalarRestriction_apply]
  exact character_sum χ _

theorem character_expectation_product (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (eval : Ω → H) (χ : AddChar F2 ℝ)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) :
    (hiddenTapeLaw W μ).expectation (fun ω => χ (Φ (hiddenSum W eval ω))) =
      ∏ v : HiddenDirection W,
        μ.expectation (fun ω => χ (scalarRestriction W Φ (directionIn W v) (eval ω))) := by
  let f : HiddenDirection W → Ω → ℝ :=
    fun v ω => χ (scalarRestriction W Φ (directionIn W v) (eval ω))
  have hprod := FiniteProduct.expectation_product
    (I := HiddenDirection W) (Ω := fun _ : HiddenDirection W => Ω)
    (fun _ : HiddenDirection W => μ) f
  calc
    _ = (hiddenTapeLaw W μ).expectation (fun ω => ∏ v : HiddenDirection W, f v (ω v)) :=
      FiniteDistribution.expectation_congr _ (fun ω => character_hiddenSum W eval χ Φ ω)
    _ = _ := hprod

theorem abs_expectation_character_le_one (μ : FiniteDistribution Ω)
    (χ : AddChar F2 ℝ) (f : Ω → F2) : |μ.expectation (fun ω => χ (f ω))| ≤ 1 := by
  calc
    _ ≤ ∑ ω, |μ.weight ω * χ (f ω)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ ω, μ.weight ω := by
      apply Finset.sum_congr rfl
      intro ω _
      rw [abs_mul, abs_of_nonneg (μ.nonnegative ω), abs_character, mul_one]
    _ = 1 := μ.normalized

theorem hidden_bias_le (W : Submodule F2 (Fin ℓ → F2))
    (μ : FiniteDistribution Ω) (eval : Ω → H) (χ : AddChar F2 ℝ) (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 H, f ≠ 0 →
      |μ.expectation (fun ω => χ (f (eval ω)))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    |(hiddenTapeLaw W μ).expectation (fun ω => χ (Φ (hiddenSum W eval ω)))| ≤ bound := by
  obtain ⟨v, hv⟩ := exists_nonzero_restriction W Φ hΦ
  rw [character_expectation_product, Finset.abs_prod]
  let a : HiddenDirection W → ℝ := fun w =>
    |μ.expectation (fun ω => χ (scalarRestriction W Φ (directionIn W w) (eval ω)))|
  change (∏ w, a w) ≤ bound
  rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ v)]
  have hrest : (∏ w ∈ Finset.univ.erase v, a w) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun w _ => abs_expectation_character_le_one μ χ _)
  calc
    _ ≤ a v * 1 := mul_le_mul_of_nonneg_left hrest (abs_nonneg _)
    _ = a v := mul_one _
    _ ≤ bound := scalar_bias _ hv

theorem law_bias_le (W : Submodule F2 (Fin ℓ → F2)) [Finite H]
    (μ : FiniteDistribution Ω) (eval : Ω → H) (χ : AddChar F2 ℝ) (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 H, f ≠ 0 →
      |μ.expectation (fun ω => χ (f (eval ω)))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    |(law W μ eval).expectation (fun x => χ (Φ x))| ≤ bound := by
  rw [law, FiniteDistribution.expectation_pushforward]
  exact hidden_bias_le W μ eval χ bound scalar_bias Φ hΦ

theorem law_sign_bias_le (W : Submodule F2 (Fin ℓ → F2)) [Finite H]
    (μ : FiniteDistribution Ω) (eval : Ω → H) (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 H, f ≠ 0 →
      |μ.expectation (fun ω => QuarterBalance.sign (f (eval ω)))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (hΦ : Φ ≠ 0) :
    |(law W μ eval).expectation (fun x => QuarterBalance.sign (Φ x))| ≤ bound :=
  law_bias_le W μ eval signCharacter bound scalar_bias Φ hΦ

section Recursive

universe u
variable {branch : Nat → Nat} {n m : Nat}

theorem recursive_law_sign_bias_le (W : Submodule F2 (Fin ℓ → F2)) (repeats : Nat → Nat)
    (p : DescendantSpaces.Path branch n m) (A : RecursiveSpaces.Slots branch n → Type u)
    [∀ s, Finite (A s)] [Fintype (RecursiveSpaces.space F2 branch n A)]
    (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 (RecursiveSpaces.space F2 branch n A), f ≠ 0 →
      |(RecursiveSampler.law F2 repeats p A).expectation
        (fun h => QuarterBalance.sign (f h))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] RecursiveSpaces.space F2 branch n A)) (hΦ : Φ ≠ 0) :
    |(recursiveLaw W repeats p A).expectation (fun x => QuarterBalance.sign (Φ x))| ≤ bound := by
  apply law_sign_bias_le W (RecursiveSampler.tapeLaw F2 repeats p A)
    (RecursiveSampler.evaluate F2 repeats p A) bound ?_ Φ hΦ
  intro f hf
  simpa only [RecursiveSampler.law, FiniteDistribution.expectation_pushforward] using
    scalar_bias f hf

end Recursive


end

end PerfectCompleteness.HiddenBucketBias

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputReferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

theorem mem_heavyList (repeats : Nat → Nat) (cut : Cut upper lower)
    (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
    (input : Input slots rows upper lower W a)
    (σ : Module.Dual F2 (UpperVector rows upper)) (threshold : ℝ)
    (Φ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) :
    Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ↔
      threshold ≤ |(referenceLaw slots rows upper lower W repeats cut).expectation
        (fun X => QuarterBalance.sign (σ (response slots rows upper lower W a labeling input X)) *
          QuarterBalance.sign (Φ X))| := by
  simp only [heavyList, SmallBias.heavySet, Finset.mem_filter, Finset.mem_univ, true_and]

end
end PerfectCompleteness.OwnInputReference



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatent
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.Runtime.haltedOutputLength _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id _root_.OAI.UniqueGamesTheorem.Foundations.Repetition.revealFirstLaw_weight
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_FiniteListSampling
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_RationalFiniteLawLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSamplerBiasProducts

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]

theorem pairTape_law (R : Nat) (μ : FiniteDistribution V) :
    (FiniteProduct.law (fun _ : Fin R × Bool => μ)).pushforward (pairTapeEquiv R V) =
      FiniteProduct.law (fun _ : Fin R => μ.product μ) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  change (∏ hb : Fin R × Bool,
      μ.weight (if hb.2 then (y hb.1).2 else (y hb.1).1)) =
    ∏ h : Fin R, μ.weight (y h).1 * μ.weight (y h).2
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro h _
  simp [mul_comm]

theorem expectation_pairs (R : Nat) (μ : FiniteDistribution V) (φ : V × V → ℝ) :
    (FiniteProduct.law (fun _ : Fin R × Bool => μ)).expectation
        (fun x => ∏ h : Fin R, φ (x (h, false), x (h, true))) =
      ((μ.product μ).expectation φ) ^ R := by
  calc
    _ = ((FiniteProduct.law (fun _ : Fin R × Bool => μ)).pushforward
        (pairTapeEquiv R V)).expectation (fun y => ∏ h : Fin R, φ (y h)) :=
      (FiniteDistribution.expectation_pushforward _ _ _).symm
    _ = (FiniteProduct.law (fun _ : Fin R => μ.product μ)).expectation
        (fun y => ∏ h : Fin R, φ (y h)) := by rw [pairTape_law]
    _ = ∏ _h : Fin R, (μ.product μ).expectation φ :=
      FiniteProduct.expectation_product _ (fun _ => φ)
    _ = _ := by simp

theorem expectation_product_mul (μ : FiniteDistribution V) (ν : FiniteDistribution W)
    (f : V → ℝ) (g : W → ℝ) :
    (μ.product ν).expectation (fun z => f z.1 * g z.2) =
      μ.expectation f * ν.expectation g := by
  change (∑ z : V × W, (μ.weight z.1 * ν.weight z.2) * (f z.1 * g z.2)) =
    (∑ v : V, μ.weight v * f v) * (∑ w : W, ν.weight w * g w)
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro w _
  exact mul_mul_mul_comm _ _ _ _

end
end PerfectCompleteness.RecursiveSamplerBiasProducts



noncomputable section

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

namespace PerfectCompleteness.FiniteProduct

variable {I : Type*} [Fintype I] [DecidableEq I]
  {Ω Γ : I → Type*} [∀ i, Fintype (Ω i)] [∀ i, Fintype (Γ i)]

theorem pushforward_map (P : (i : I) → FiniteDistribution (Ω i))
    (f : (i : I) → Ω i → Γ i) :
    (law P).pushforward (fun x i => f i (x i)) =
      law (fun i => (P i).pushforward (f i)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro y
  simp only [FiniteDistribution.pushforward, law]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff]

end PerfectCompleteness.FiniteProduct

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BucketUniformLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OriginalCutCalls.indexFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexDecidableEq _root_.OAI.PerfectCompleteness.TerminalCalls.terminalIndexFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutCalls.indexFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.RecursiveSamplerBiasAlgebra

open PointwiseSpaces RecursiveSpaces RecursiveSampler
open scoped BigOperators

universe u w

variable (𝕜 : Type w) [Field 𝕜]

theorem square_functional_eq_zero_of_products {X : Type u}
    (H : Submodule 𝕜 (X → 𝕜)) (L : squareSpace H →ₗ[𝕜] 𝕜)
    (hL : ∀ g h : H, L (squareProduct 𝕜 H g h) = 0) : L = 0 := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  change L ⟨x, hx⟩ = 0
  refine Submodule.span_induction
    (p := fun y hy => L ⟨y, hy⟩ = 0) ?_ ?_ ?_ ?_ hx
  · rintro y ⟨g, hg, h, hh, rfl⟩
    exact hL ⟨g, hg⟩ ⟨h, hh⟩
  · exact map_zero L
  · intro y z hy hz hLy hLz
    change L ((⟨y, hy⟩ : squareSpace H) + ⟨z, hz⟩) = 0
    rw [map_add, hLy, hLz, add_zero]
  · intro c y hy hLy
    change L (c • (⟨y, hy⟩ : squareSpace H)) = 0
    rw [map_smul, hLy, smul_zero]

variable {branch : Nat → Nat} {n : Nat}

theorem eq_zero_of_child_restrictions (A : Slots branch (n + 1) → Type u)
    (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜)
    (hzero : ∀ i : Fin (branch n), f.comp (childSquareLift 𝕜 A i) = 0) : f = 0 := by
  apply LinearMap.ext
  rintro ⟨x, hx⟩
  change f ⟨x, hx⟩ = 0
  refine Submodule.iSup_induction'
    (fun i : Fin (branch n) =>
      (squareSpace (space 𝕜 branch n (childFamily A i))).map
        (pullback 𝕜 (childRestriction A i)))
    (motive := fun y hy => f ⟨y, hy⟩ = 0) ?_ ?_ ?_ hx
  · intro i y hy
    obtain ⟨g, hg, rfl⟩ := Submodule.mem_map.mp hy
    exact LinearMap.congr_fun (hzero i) ⟨g, hg⟩
  · exact map_zero f
  · intro y z hy hz hfy hfz
    change f ((⟨y, hy⟩ : space 𝕜 branch (n + 1) A) + ⟨z, hz⟩) = 0
    rw [map_add, hfy, hfz, add_zero]

theorem exists_child_restriction_ne_zero (A : Slots branch (n + 1) → Type u)
    (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜) (hf : f ≠ 0) :
    ∃ i : Fin (branch n), f.comp (childSquareLift 𝕜 A i) ≠ 0 := by
  classical
  by_contra h
  apply hf
  apply eq_zero_of_child_restrictions 𝕜 A f
  intro i
  by_contra hi
  exact h ⟨i, hi⟩

theorem childBilinear_ne_zero (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜)
    (hchild : f.comp (childSquareLift 𝕜 A i) ≠ 0) :
    childBilinear 𝕜 A i f ≠ 0 := by
  intro hzero
  apply hchild
  apply square_functional_eq_zero_of_products 𝕜 _ _
  intro g h
  exact LinearMap.congr_fun₂ hzero g h

theorem ordinary_or_bilinear_ne_zero (A : Slots branch (n + 1) → Type u)
    (i : Fin (branch n)) (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜) (hf : f ≠ 0) :
    (∃ j : OffPath i, f.comp (childSquareLift 𝕜 A j.val) ≠ 0) ∨
      childBilinear 𝕜 A i f ≠ 0 := by
  classical
  obtain ⟨j, hj⟩ := exists_child_restriction_ne_zero 𝕜 A f hf
  by_cases hji : j = i
  · subst j
    exact Or.inr (childBilinear_ne_zero 𝕜 A i f hj)
  · exact Or.inl ⟨⟨j, hji⟩, hj⟩

noncomputable section

theorem combine_eq (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (r : Nat)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    combine 𝕜 A i r ordinary left right =
      (∑ j : OffPath i, childSquareLift 𝕜 A j.val (ordinary j)) +
        ∑ h : Fin r, childProduct 𝕜 A i (left h) (right h) := by
  apply Subtype.ext
  change combineFunction 𝕜 A i r ordinary left right =
    (space 𝕜 branch (n + 1) A).subtype
      ((∑ j : OffPath i, childSquareLift 𝕜 A j.val (ordinary j)) +
        ∑ h : Fin r, childProduct 𝕜 A i (left h) (right h))
  rw [map_add, map_sum, map_sum]
  rfl

theorem map_combine (A : Slots branch (n + 1) → Type u) (i : Fin (branch n))
    (r : Nat) (f : space 𝕜 branch (n + 1) A →ₗ[𝕜] 𝕜)
    (ordinary : (j : OffPath i) → squareSpace (space 𝕜 branch n (childFamily A j.val)))
    (left right : Fin r → space 𝕜 branch n (childFamily A i)) :
    f (combine 𝕜 A i r ordinary left right) =
      (∑ j : OffPath i, (f.comp (childSquareLift 𝕜 A j.val)) (ordinary j)) +
        ∑ h : Fin r, childBilinear 𝕜 A i f (left h) (right h) := by
  rw [combine_eq, map_add, map_sum, map_sum]
  rfl

end
end PerfectCompleteness.RecursiveSamplerBiasAlgebra



namespace PerfectCompleteness.RecursiveSampler

open PointwiseSpaces RecursiveSpaces DescendantSpaces
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

universe u w

variable {branch : Nat → Nat} {n m : Nat}

variable (𝕜 : Type w) [Field 𝕜]

noncomputable section

variable [Finite 𝕜]

theorem splitTape_law (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] :
    (tapeLaw 𝕜 repeats (.step i p) A).pushforward (splitTapeEquiv 𝕜 repeats i p A) =
      (ordinaryLaw 𝕜 repeats i p A).product (callTapeLaw 𝕜 repeats i p A) := by
  rw [← FiniteDistribution.transport_eq_pushforward]
  apply FiniteDistribution.eq_of_weight_eq
  intro z
  let : ∀ j : OffPath i ⊕ (CallIndex repeats n × DrawIndex repeats p),
      Fintype (DrawSpace 𝕜 repeats (.step i p) A j) :=
    fun j => drawSpaceFintype 𝕜 repeats (.step i p) A j
  change
    (∏ j : OffPath i ⊕ (CallIndex repeats n × DrawIndex repeats p),
      1 / (Fintype.card (DrawSpace 𝕜 repeats (.step i p) A j) : ℝ)) =
    (∏ j : OffPath i,
      1 / (Fintype.card (DrawSpace 𝕜 repeats (.step i p) A (.inl j)) : ℝ)) *
      ∏ _hb : CallIndex repeats n, ∏ j : DrawIndex repeats p,
        1 / (Fintype.card (DrawSpace 𝕜 repeats p (childFamily A i) j) : ℝ)
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  simp only [Fintype.card_eq_nat_card]
  rfl

theorem evaluateCalls_law (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space 𝕜 branch n (childFamily A i))] :
    (callTapeLaw 𝕜 repeats i p A).pushforward (evaluateCalls 𝕜 repeats i p A) =
      callScalarLaw 𝕜 repeats i p A :=
  FiniteProduct.pushforward_map _ (fun _ => evaluate 𝕜 repeats p (childFamily A i))

theorem splitEvaluatedTape_law (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space 𝕜 branch n (childFamily A i))] :
    (tapeLaw 𝕜 repeats (.step i p) A).pushforward
        (splitEvaluatedTape 𝕜 repeats i p A) =
      (ordinaryLaw 𝕜 repeats i p A).product (callScalarLaw 𝕜 repeats i p A) := by
  calc
    _ = ((tapeLaw 𝕜 repeats (.step i p) A).pushforward
        (splitTapeEquiv 𝕜 repeats i p A)).pushforward
          (fun z => (z.1, evaluateCalls 𝕜 repeats i p A z.2)) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = ((ordinaryLaw 𝕜 repeats i p A).product
        (callTapeLaw 𝕜 repeats i p A)).pushforward
          (fun z => (z.1, evaluateCalls 𝕜 repeats i p A z.2)) := by
      rw [splitTape_law]
    _ = (ordinaryLaw 𝕜 repeats i p A).product
        ((callTapeLaw 𝕜 repeats i p A).pushforward
          (evaluateCalls 𝕜 repeats i p A)) := by
      simpa only [id_eq, FiniteDistribution.pushforward_id] using
        (FiniteDistribution.product_pushforward
          (ordinaryLaw 𝕜 repeats i p A) (callTapeLaw 𝕜 repeats i p A)
          (id : OrdinaryTape 𝕜 repeats i p A → OrdinaryTape 𝕜 repeats i p A)
          (evaluateCalls 𝕜 repeats i p A))
    _ = _ := by rw [evaluateCalls_law]

theorem law_step (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space 𝕜 branch n (childFamily A i))]
    [Fintype (space 𝕜 branch (n + 1) A)] :
    law 𝕜 repeats (.step i p) A =
      ((ordinaryLaw 𝕜 repeats i p A).product
        (callScalarLaw 𝕜 repeats i p A)).pushforward
          (stepCombine 𝕜 repeats i p A) := by
  calc
    _ = ((tapeLaw 𝕜 repeats (.step i p) A).pushforward
        (splitEvaluatedTape 𝕜 repeats i p A)).pushforward
          (stepCombine 𝕜 repeats i p A) :=
      (FiniteDistribution.pushforward_comp _ _ _).symm
    _ = _ := by rw [splitEvaluatedTape_law]

end
end PerfectCompleteness.RecursiveSampler

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_UniformLatentSupportLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.stepFactorFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.AffineLinearHeavyWitness.card_badMasks _root_.OAI.PerfectCompleteness.AffineLinearHeavyWitness.mem_badMasks _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.abs_character _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.bitSign_toBool _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.character_zero _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.frequency_apply_basis _root_.OAI.PerfectCompleteness.BinaryDualCoordinates.ofBool_toBool _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_refl_right _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.append_step _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NodeEmbedding.embed_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.embeddedRows_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.equiv_apply _root_.OAI.PerfectCompleteness.NodeEmbedding.matrix_evaluate _root_.OAI.PerfectCompleteness.NodeEmbedding.rowsEquiv_apply _root_.OAI.PerfectCompleteness.OddListExtraction.form_atom_self _root_.OAI.PerfectCompleteness.OddListExtraction.multiplicationForm_apply _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.UniformChildSum.childSum_apply _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.QuarterBalance

open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]

theorem nonzero_linear_surjective (f : V →ₗ[F2] F2) (hf : f ≠ 0) :
    Function.Surjective f := by
  classical
  have hx : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext h)
  obtain ⟨x, hx⟩ := hx
  intro b
  refine ⟨(b / f x) • x, ?_⟩
  simp only [map_smul, smul_eq_mul]
  exact div_mul_cancel₀ b hx

theorem uniform_bit_probability (f : V →ₗ[F2] F2) (hf : f ≠ 0) (b : F2) :
    (FiniteDistribution.uniform V).probability (fun x => decide (f x = b)) = (1 / 2 : ℝ) := by
  have h := UniformLinearImage.uniform_pushforward_linearMap f (nonzero_linear_surjective f hf)
  have hp := congrArg (fun μ : FiniteDistribution F2 =>
    μ.probability (fun y => decide (y = b))) h
  rw [FiniteDistribution.probability_pushforward] at hp
  rw [hp, UniformLatent.probability_uniform_singleton]
  norm_num [F2, ZMod.card]

theorem uniform_sign_expectation_eq_zero (f : V →ₗ[F2] F2) (hf : f ≠ 0) :
    (FiniteDistribution.uniform V).expectation (fun x => sign (f x)) = 0 := by
  rw [expectation_sign, uniform_bit_probability f hf]
  norm_num

end
end PerfectCompleteness.QuarterBalance



namespace PerfectCompleteness.RecursiveSamplerBias

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PointwiseSpaces RecursiveSpaces DescendantSpaces RecursiveSampler QuarterBalance
open RecursiveSamplerBiasAlgebra RecursiveSamplerBiasProducts

noncomputable section

universe u

variable {branch : Nat → Nat} {n m : Nat}

theorem sign_sum {I : Type*} [Fintype I] (a : I → F2) :
    sign (∑ i, a i) = ∏ i, sign (a i) := by
  classical
  have h (s : Finset I) : sign (∑ i ∈ s, a i) = ∏ i ∈ s, sign (a i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
        rw [Finset.sum_insert hi, Finset.prod_insert hi, sign_add, ih]
  exact h Finset.univ

theorem abs_expectation_sign_le_one {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → F2) :
    |μ.expectation (fun x => sign (f x))| ≤ 1 := by
  calc
    _ ≤ ∑ x, |μ.weight x * sign (f x)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, μ.weight x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [abs_mul, abs_of_nonneg (μ.nonnegative x), abs_sign, mul_one]
    _ = 1 := μ.normalized

theorem law_step_character (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n (childFamily A i))]
    [Fintype (space F2 branch (n + 1) A)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) :
    (law F2 repeats (.step i p) A).expectation (fun g => sign (f g)) =
      ordinaryCharacterMean repeats i p A f *
        pairCharacterMean repeats i p A f ^ repeats (n + 1) := by
  classical
  let : ∀ j : OffPath i, Fintype (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    fun j => drawSpaceFintype F2 repeats (.step i p) A (.inl j)
  let : ∀ j : OffPath i, Nonempty (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    fun j => ⟨zeroDraw F2 repeats (.step i p) A (.inl j)⟩
  rw [law_step, FiniteDistribution.expectation_pushforward]
  have hsign (z : OrdinaryTape F2 repeats i p A ×
      (CallIndex repeats n → space F2 branch n (childFamily A i))) :
      sign (f (stepCombine F2 repeats i p A z)) =
        (∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (z.1 j))) *
          ∏ h : Fin (repeats (n + 1)),
            sign (childBilinear F2 A i f (z.2 (h, false)) (z.2 (h, true))) := by
    have hm := map_combine F2 A i (repeats (n + 1)) f
      (fun j : OffPath i =>
        (show squareSpace (space F2 branch n (childFamily A j.val)) from z.1 j))
      (fun h => z.2 (h, false)) (fun h => z.2 (h, true))
    calc
      _ = sign ((∑ j : OffPath i, (f.comp (childSquareLift F2 A j.val)) (z.1 j)) +
          ∑ h : Fin (repeats (n + 1)),
            childBilinear F2 A i f (z.2 (h, false)) (z.2 (h, true))) := congrArg sign hm
      _ = _ := by rw [sign_add, sign_sum, sign_sum]
  have hord : (ordinaryLaw F2 repeats i p A).expectation
      (fun o => ∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (o j))) =
      ordinaryCharacterMean repeats i p A f :=
    FiniteProduct.expectation_product
      (I := OffPath i)
      (Ω := fun j => DrawSpace F2 repeats (.step i p) A (.inl j))
      (fun j : OffPath i =>
        FiniteDistribution.uniform (DrawSpace F2 repeats (.step i p) A (.inl j)))
      (fun j (g : DrawSpace F2 repeats (.step i p) A (.inl j)) =>
        sign ((f.comp (childSquareLift F2 A j.val)) g))
  have hpair : (callScalarLaw F2 repeats i p A).expectation
      (fun x => ∏ h : Fin (repeats (n + 1)),
        sign (childBilinear F2 A i f (x (h, false)) (x (h, true)))) =
      pairCharacterMean repeats i p A f ^ repeats (n + 1) :=
    expectation_pairs (repeats (n + 1)) (law F2 repeats p (childFamily A i))
      (fun z => sign (childBilinear F2 A i f z.1 z.2))
  calc
    _ = ((ordinaryLaw F2 repeats i p A).product
        (callScalarLaw F2 repeats i p A)).expectation
          (fun z =>
            (∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (z.1 j))) *
              ∏ h : Fin (repeats (n + 1)),
                sign (childBilinear F2 A i f (z.2 (h, false)) (z.2 (h, true)))) :=
      FiniteDistribution.expectation_congr _ hsign
    _ = (ordinaryLaw F2 repeats i p A).expectation
          (fun o => ∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (o j))) *
        (callScalarLaw F2 repeats i p A).expectation
          (fun x => ∏ h : Fin (repeats (n + 1)),
            sign (childBilinear F2 A i f (x (h, false)) (x (h, true)))) :=
      expectation_product_mul
        (V := OrdinaryTape F2 repeats i p A)
        (W := CallIndex repeats n → space F2 branch n (childFamily A i))
        (ordinaryLaw F2 repeats i p A) (callScalarLaw F2 repeats i p A)
        (fun o : OrdinaryTape F2 repeats i p A =>
          ∏ j : OffPath i, sign ((f.comp (childSquareLift F2 A j.val)) (o j)))
        (fun x : CallIndex repeats n → space F2 branch n (childFamily A i) =>
          ∏ h : Fin (repeats (n + 1)),
            sign (childBilinear F2 A i f (x (h, false)) (x (h, true))))
    _ = _ := congrArg₂ (fun a b : ℝ => a * b) hord hpair

theorem abs_ordinaryCharacterMean_le_one (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) :
    |ordinaryCharacterMean repeats i p A f| ≤ 1 := by
  unfold ordinaryCharacterMean
  rw [Finset.abs_prod]
  apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
  intro j _
  let : Fintype (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    drawSpaceFintype F2 repeats (.step i p) A (.inl j)
  let : Nonempty (DrawSpace F2 repeats (.step i p) A (.inl j)) :=
    ⟨zeroDraw F2 repeats (.step i p) A (.inl j)⟩
  exact abs_expectation_sign_le_one
    (FiniteDistribution.uniform (DrawSpace F2 repeats (.step i p) A (.inl j)))
    (fun g => (f.comp (childSquareLift F2 A j.val)) g)

theorem ordinaryCharacterMean_eq_zero (repeats : Nat → Nat)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2)
    (j : OffPath i) (hj : f.comp (childSquareLift F2 A j.val) ≠ 0) :
    ordinaryCharacterMean repeats i p A f = 0 := by
  classical
  unfold ordinaryCharacterMean
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  let : Fintype (squareSpace (space F2 branch n (childFamily A j.val))) :=
    drawSpaceFintype F2 repeats (.step i p) A (.inl j)
  exact uniform_sign_expectation_eq_zero (f.comp (childSquareLift F2 A j.val)) hj

theorem law_step_bias_le (repeats : Nat → Nat) (i : Fin (branch n))
    (p : Path branch n m) (A : Slots branch (n + 1) → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n (childFamily A i))]
    [Fintype (space F2 branch (n + 1) A)]
    (hchild : Balanced (law F2 repeats p (childFamily A i)))
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) (hf : f ≠ 0) :
    |(law F2 repeats (.step i p) A).expectation (fun g => sign (f g))| ≤
      (7 / 8 : ℝ) ^ repeats (n + 1) := by
  rw [law_step_character]
  rcases ordinary_or_bilinear_ne_zero F2 A i f hf with ⟨j, hj⟩ | hB
  · rw [ordinaryCharacterMean_eq_zero repeats i p A f j hj, zero_mul, abs_zero]
    exact pow_nonneg (by norm_num) _
  · have hp : |pairCharacterMean repeats i p A f| ≤ (7 / 8 : ℝ) :=
      bilinear_bias _ _ hchild hchild (childBilinear F2 A i f) hB
    rw [abs_mul, abs_pow]
    calc
      _ ≤ 1 * |pairCharacterMean repeats i p A f| ^ repeats (n + 1) :=
        mul_le_mul_of_nonneg_right
          (abs_ordinaryCharacterMean_le_one repeats i p A f) (pow_nonneg (abs_nonneg _) _)
      _ = |pairCharacterMean repeats i p A f| ^ repeats (n + 1) := one_mul _
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hp _

theorem law_balanced (repeats : Nat → Nat) (hrep : RepetitionsBalanced repeats)
    (p : Path branch n m) :
    ∀ (A : Slots branch n → Type u) [∀ s, Finite (A s)]
      [Fintype (space F2 branch n A)], Balanced (law F2 repeats p A) := by
  induction p with
  | refl n =>
      intro A hA hH
      rw [law_refl_uniform]
      apply balanced_of_bias_le_half
      intro f hf
      rw [uniform_sign_expectation_eq_zero f hf, abs_zero]
      norm_num
  | @step n m i p ih =>
      intro A hA hH
      let : Fintype (space F2 branch n (childFamily A i)) := Fintype.ofFinite _
      have hchild := ih (childFamily A i)
      apply balanced_of_bias_le_half
      intro f hf
      exact (law_step_bias_le repeats i p A hchild f hf).trans (hrep n)

theorem law_bias_le (repeats : Nat → Nat) (hrep : RepetitionsBalanced repeats)
    (i : Fin (branch n)) (p : Path branch n m)
    (A : Slots branch (n + 1) → Type u) [∀ s, Finite (A s)]
    [Fintype (space F2 branch (n + 1) A)]
    (f : space F2 branch (n + 1) A →ₗ[F2] F2) (hf : f ≠ 0) :
    |(law F2 repeats (.step i p) A).expectation (fun g => sign (f g))| ≤
      (7 / 8 : ℝ) ^ repeats (n + 1) := by
  let : Fintype (space F2 branch n (childFamily A i)) := Fintype.ofFinite _
  exact law_step_bias_le repeats i p A
    (law_balanced repeats hrep p (childFamily A i)) f hf

theorem law_bias_le_height (repeats : Nat → Nat) (hrep : RepetitionsBalanced repeats)
    (p : Path branch n m) (A : Slots branch n → Type u)
    [∀ s, Finite (A s)] [Fintype (space F2 branch n A)]
    (f : space F2 branch n A →ₗ[F2] F2) (hf : f ≠ 0) :
    |(law F2 repeats p A).expectation (fun g => sign (f g))| ≤
      (7 / 8 : ℝ) ^ repeats n := by
  cases p with
  | refl n =>
      rw [law_refl_uniform, uniform_sign_expectation_eq_zero f hf, abs_zero]
      exact pow_nonneg (by norm_num) _
  | step i p => exact law_bias_le repeats hrep i p A f hf

end
end PerfectCompleteness.RecursiveSamplerBias

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Machines_OwnInputHeavyBounds
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OwnInputHeavyBounds

open scoped TensorProduct Classical
open TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper))

attribute [local instance] OAI.PerfectCompleteness.OwnInputHeavyBounds.upperSpaceFintype
theorem referenceLaw_sign_bias_le (repeats : Nat → Nat) (cut : Cut upper lower)
    (bound : ℝ)
    (scalar_bias : ∀ f : Module.Dual F2 (UpperSpace slots upper), f ≠ 0 →
      |(RecursiveSampler.law F2 repeats cut.path (LeafDomain (nodeSlots slots upper))).expectation
        (fun h => QuarterBalance.sign (f h))| ≤ bound)
    (Φ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper)) (hΦ : Φ ≠ 0) :
    |(referenceLaw slots rows upper lower W repeats cut).expectation
      (fun X => QuarterBalance.sign (Φ X))| ≤ bound :=
  HiddenBucketBias.recursive_law_sign_bias_le W repeats cut.path
    (LeafDomain (nodeSlots slots upper)) bound scalar_bias Φ hΦ

end

end PerfectCompleteness.OwnInputHeavyBounds

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_BoundedListSamplingLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.BoundedListSampling

noncomputable section

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

variable {Index A : Type*} [Fintype A]

theorem listLaw_of_nonempty (L : Finset A) (default : A) (h : L.Nonempty) :
    listLaw L default = FiniteListSampling.uniformList L h := by
  simp [listLaw, h]

theorem listLaw_weight_mem (L : Finset A) (default a : A) (ha : a ∈ L) :
    (listLaw L default).weight a = 1 / (L.card : ℝ) := by
  rw [listLaw_of_nonempty L default ⟨a, ha⟩]
  exact FiniteListSampling.uniformList_weight_mem L ⟨a, ha⟩ a ha

theorem listLaw_weight_lower (L : Finset A) (default : A) (M : ℝ)
    (hM : 0 < M) (hcard : (L.card : ℝ) ≤ M) (a : A) (ha : a ∈ L) :
    1 / M ≤ (listLaw L default).weight a := by
  rw [listLaw_weight_mem L default a ha]
  have hcardPos : 0 < (L.card : ℝ) := Nat.cast_pos.mpr (Finset.Nonempty.card_pos ⟨a, ha⟩)
  apply (div_le_div_iff₀ hM hcardPos).mpr
  simpa only [one_mul] using hcard

variable [Fintype Index] [Nonempty Index]

theorem jointLaw_weight_ge_of_mem (L : Index → Finset A) (default : A) (M : ℝ)
    (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (σ : Index) (a : A) (ha : a ∈ L σ) :
    1 / ((Fintype.card Index : ℝ) * M) ≤ (jointLaw L default).weight (σ, a) := by
  rw [jointLaw_weight, ← one_div_mul_one_div]
  exact mul_le_mul_of_nonneg_left (listLaw_weight_lower (L σ) default M hM (hcard σ) a ha)
    (one_div_nonneg.mpr (Nat.cast_nonneg _))

theorem joint_success_lower (L : Index → Finset A) (default : A) (M : ℝ)
    (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (event : Index × A → Bool) (witness : ∃ σ a, a ∈ L σ ∧ event (σ, a) = true) :
    1 / ((Fintype.card Index : ℝ) * M) ≤ (jointLaw L default).probability event := by
  obtain ⟨σ, a, ha, hevent⟩ := witness
  exact (jointLaw_weight_ge_of_mem L default M hM hcard σ a ha).trans
    (FiniteListSampling.probability_ge_weight (jointLaw L default) event (σ, a) hevent)

theorem outputLaw_probability {B : Type*} [Fintype B]
    (L : Index → Finset A) (default : A) (decode : Index → A → B) (event : B → Bool) :
    (outputLaw L default decode).probability event =
      (jointLaw L default).probability (fun p => event (decode p.1 p.2)) :=
  FiniteDistribution.probability_pushforward _ _ _

theorem output_success_lower {B : Type*} [Fintype B]
    (L : Index → Finset A) (default : A) (decode : Index → A → B)
    (M : ℝ) (hM : 0 < M) (hcard : ∀ σ, ((L σ).card : ℝ) ≤ M)
    (event : B → Bool)
    (witness : ∃ σ a, a ∈ L σ ∧ event (decode σ a) = true) :
    1 / ((Fintype.card Index : ℝ) * M) ≤ (outputLaw L default decode).probability event := by
  rw [outputLaw_probability]
  exact joint_success_lower L default M hM hcard _ witness

end
end PerfectCompleteness.BoundedListSampling



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RightDecoderLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DescriptorProjectionMachine.outputWords_length _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LevelPairCounting.pairProbability_self _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceIDs_tuple _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.questionToTuple_tupleToQuestion _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_length _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RightDecoder

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)

variable (repeats : Nat → Nat) (cut : Cut upper lower)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (input : Input slots rows upper lower W a) (threshold : ℝ)

attribute [local instance] OAI.PerfectCompleteness.RightDecoder.characterFintype
attribute [local instance] OAI.PerfectCompleteness.RightDecoder.scalarFintype
theorem success_lower (M : ℝ) (hM : 0 < M)
    (hcard : ∀ σ : Module.Dual F2 (UpperVector rows upper),
      ((heavyList slots rows upper lower W a repeats cut labeling input σ threshold).card : ℝ) ≤ M)
    (event : Module.Dual F2 (UpperSpace slots upper) → Bool)
    (witness : ∃ σ Φ,
      Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ∧
      event (DecoderContraction.contract W σ Φ) = true) :
    1 / ((Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ) * M) ≤
      (law slots rows upper lower W a repeats cut labeling input threshold).probability event := by
  exact BoundedListSampling.output_success_lower
    (fun σ => heavyList slots rows upper lower W a repeats cut labeling input σ threshold)
    0 (DecoderContraction.contract W) M hM hcard event witness

theorem coset_lower (M : ℝ) (hM : 0 < M)
    (hcard : ∀ σ : Module.Dual F2 (UpperVector rows upper),
      ((heavyList slots rows upper lower W a repeats cut labeling input σ threshold).card : ℝ) ≤ M)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (z : Module.Dual F2 (UpperSpace slots upper))
    (witness : ∃ σ Φ,
      Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ∧
      σ.comp W.subtype ≠ 0 ∧
      Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q) :
    1 / ((Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ) * M) ≤
      (law slots rows upper lower W a repeats cut labeling input threshold).probability
        (fun decoded => decide (decoded - z ∈ Q)) := by
  apply success_lower slots rows upper lower W a repeats cut labeling input threshold M hM hcard
  obtain ⟨σ, Φ, hlist, hσ, hΦ⟩ := witness
  exact ⟨σ, Φ, hlist, by
    simpa only [decide_eq_true_eq] using
      DecoderContraction.contract_sub_mem W Q σ Φ z hσ hΦ⟩

theorem coset_lower_of_balanced
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hthreshold : 0 < threshold)
    (hsmall : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ threshold ^ 2 / 2)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (z : Module.Dual F2 (UpperSpace slots upper))
    (witness : ∃ σ Φ,
      Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ threshold ∧
      σ.comp W.subtype ≠ 0 ∧
      Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q) :
    threshold ^ 2 /
        (2 * (Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ)) ≤
      (law slots rows upper lower W a repeats cut labeling input threshold).probability
        (fun decoded => decide (decoded - z ∈ Q)) := by
  have hsq : 0 < threshold ^ 2 := sq_pos_of_pos hthreshold
  have hcard : ∀ σ : Module.Dual F2 (UpperVector rows upper),
      ((heavyList slots rows upper lower W a repeats cut labeling input σ threshold).card : ℝ) ≤
        2 / threshold ^ 2 := by
    intro σ
    exact OwnInputHeavyBounds.heavyList_card_le_of_balanced slots rows upper lower W a
      repeats cut hrep labeling input σ threshold hthreshold hsmall
  have h := coset_lower slots rows upper lower W a repeats cut labeling input threshold
    (2 / threshold ^ 2) (div_pos (by norm_num) hsq) hcard Q z witness
  have hcount :
      (Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have heq :
      1 / ((Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ) *
        (2 / threshold ^ 2)) =
      threshold ^ 2 / (2 * (Fintype.card (Module.Dual F2 (UpperVector rows upper)) : ℝ)) := by
    field_simp [hcount, ne_of_gt hsq]
  rwa [heq] at h

end
end PerfectCompleteness.RightDecoder



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_OutputAnnihilator
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.OutputAnnihilator

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Integration.BinaryLinear (F2)

variable {K : Type*} [AddCommGroup K] [Module F2 K]
  [FiniteDimensional F2 K] [Fintype (Module.Dual F2 K)]

omit [FiniteDimensional F2 K] in
theorem card_dual : Fintype.card (Module.Dual F2 K) = 2 ^ Module.finrank F2 K := by
  rw [Module.card_eq_pow_finrank (K := F2), Subspace.dual_finrank_eq]
  rw [show Fintype.card F2 = 2 by decide]

end
end PerfectCompleteness.OutputAnnihilator

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Sampling_OwnLawHeavyList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.OwnLawHeavyList

open QuarterBalance
open HiddenBucketBias (recursiveLaw)
open UniqueGamesTheorem.Foundations.Games
open scoped TensorProduct Classical

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module F2 V] [Fintype V]

attribute [local instance] OAI.PerfectCompleteness.OwnLawHeavyList.dualFintype
theorem mem_heavyList (μ : FiniteDistribution V) (target : V → ℝ) (threshold : ℝ)
    (f : Module.Dual F2 V) :
    f ∈ heavyList μ target threshold ↔
      threshold ≤ |μ.expectation (fun x => target x * character f x)| := by
  simp only [heavyList, SmallBias.heavySet, Finset.mem_filter, Finset.mem_univ, true_and]

universe u

end
end PerfectCompleteness.OwnLawHeavyList

end

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Decoding_RightDecoderWitness
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DescriptorProjectionMachine.outputWords_length _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceIDs_tuple _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.questionToTuple_tupleToQuestion _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_length _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.RightDecoderWitness

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TensorCosetEvaluation
open TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

section Algebra

variable {K H : Type*} [AddCommGroup K] [Module F2 K]
  [AddCommGroup H] [Module F2 H]

theorem scalarRestriction_row_add (W : Submodule F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (u v : W) :
    scalarRestriction Φ (u + v) = scalarRestriction Φ u + scalarRestriction Φ v := by
  ext h
  simp only [scalarRestriction_apply, TensorProduct.add_tmul, map_add, LinearMap.add_apply]

theorem errorSpace_of_normalized_rows (W : Submodule F2 K)
    (Q : Submodule F2 (Module.Dual F2 H)) (σ : Module.Dual F2 K)
    (Φ : Module.Dual F2 (W ⊗[F2] H)) (z : Module.Dual F2 H)
    (hσ : σ.comp W.subtype ≠ 0)
    (hgood : ∀ w : W, σ w.val = 1 → scalarRestriction Φ w - z ∈ Q) :
    Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q := by
  intro w
  rw [scalarRestriction_sub]
  change scalarRestriction Φ w - scalarRestriction (pureFrequency (σ.comp W.subtype) z) w ∈ Q
  rw [scalarRestriction_pure]
  change scalarRestriction Φ w - σ w.val • z ∈ Q
  rcases UniqueGamesTheorem.Integration.BinaryLinear.scalar_cases (σ w.val) with hzero | hone
  · rw [hzero, zero_smul, sub_zero]
    let w₀ := DecoderContraction.chosenRow W σ hσ
    have hw₀ : σ w₀.val = 1 := DecoderContraction.chosenRow_value_one W σ hσ
    have hsum : σ (w₀ + w).val = 1 := by
      simp only [Submodule.coe_add, map_add, hw₀, hzero, add_zero]
    have hdifference := Q.sub_mem (hgood (w₀ + w) hsum) (hgood w₀ hw₀)
    rw [scalarRestriction_row_add] at hdifference
    have heq : (scalarRestriction Φ w₀ + scalarRestriction Φ w - z) -
        (scalarRestriction Φ w₀ - z) = scalarRestriction Φ w := by
      abel
    rwa [heq] at hdifference
  · simpa only [hone, one_smul] using hgood w hone

end Algebra

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)
  (repeats : Nat → Nat) (cut : Cut upper lower)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (input : Input slots rows upper lower W a)

attribute [local instance] OAI.PerfectCompleteness.RightDecoderWitness.upperSpaceFintype
theorem heavyList_eq (threshold : ℝ) (σ : Module.Dual F2 (UpperVector rows upper)) :
    TensorAffineHeavyWitness.heavyList W
      (referenceLaw slots rows upper lower W repeats cut)
      (response slots rows upper lower W a labeling input) threshold σ =
      heavyList slots rows upper lower W a repeats cut labeling input σ threshold := by
  ext Φ
  simp only [TensorAffineHeavyWitness.heavyList, OwnLawHeavyList.mem_heavyList,
    OwnLawHeavyList.character, OwnInputReference.mem_heavyList]

theorem exists_heavy_error_coset
    (ρ h₀ : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hsmall : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 (UpperSpace slots upper))
    (offset : UpperVector rows upper)
    (hmatch : ρ ≤ conditionalMatch slots rows upper lower W a repeats cut labeling input
      Q target z offset) :
    ∃ σ : Module.Dual F2 (UpperVector rows upper), σ.comp W.subtype ≠ 0 ∧
      ∃ Φ ∈ heavyList slots rows upper lower W a repeats cut labeling input σ (ρ * h₀ / 4),
        Φ - DecoderContraction.baseFrequency W σ z ∈ DecoderContraction.errorSpace W Q := by
  have hbias : ∀ Φ : Module.Dual F2 (W ⊗[F2] UpperSpace slots upper), Φ ≠ 0 →
      |(referenceLaw slots rows upper lower W repeats cut).expectation
        (fun X => QuarterBalance.sign (Φ X))| ≤ (7 / 8 : ℝ) ^ repeats (Nodes.height upper) := by
    intro Φ hΦ
    apply OwnInputHeavyBounds.referenceLaw_sign_bias_le slots rows upper lower W repeats cut
      ((7 / 8 : ℝ) ^ repeats (Nodes.height upper)) ?_ Φ hΦ
    intro f hf
    exact RecursiveSamplerBias.law_bias_le_height repeats hrep cut.path
      (LeafDomain (nodeSlots slots upper)) f hf
  obtain ⟨σ, hσ, Φ, hΦ, hgood⟩ := TensorAffineHeavyWitness.exists_heavy_candidate W
    (referenceLaw slots rows upper lower W repeats cut)
    (response slots rows upper lower W a labeling input)
    ρ h₀ ((7 / 8 : ℝ) ^ repeats (Nodes.height upper)) hρ hh₀
    (pow_nonneg (by norm_num) _) hsmall hbias hexcluded Q hsize target z offset hmatch
  refine ⟨σ, hσ, Φ, ?_, errorSpace_of_normalized_rows W Q σ Φ z hσ hgood⟩
  rw [← heavyList_eq slots rows upper lower W a repeats cut labeling input]
  exact hΦ

end
end PerfectCompleteness.RightDecoderWitness

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Algebra_RightDecoderAffineSuccess
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
attribute [-simp] _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescendantSpaces.Path.slotEmbedding_append _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DescriptorProjectionMachine.outputWords_length _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.GeometricCutSplit.join_split _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_castSucc _root_.OAI.PerfectCompleteness.GeometricPath.nodeAtLevel_last _root_.OAI.PerfectCompleteness.HierarchicalKnownRows.lower_apply _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_other _root_.OAI.PerfectCompleteness.HierarchicalMatrixTable.assemble_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.ProductEvaluation.restoredRows_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceIDs_tuple _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.questionToTuple_tupleToQuestion _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_length _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PerfectCompleteness.RightDecoderAffineSuccess

open scoped TensorProduct Classical
open UniqueGamesTheorem.Foundations.Games
open TreeSourceSpaces HierarchicalArrays OwnInputReference

noncomputable section

variable {branch : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (rows : Nat → Nat) (upper lower : Nodes branch n)
  (W : Submodule F2 (UpperVector rows upper)) (a : LowerVector rows lower)
  (repeats : Nat → Nat) (cut : Cut upper lower)
  (labeling : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))
  (input : Input slots rows upper lower W a)

attribute [local instance] RightDecoder.characterFintype RightDecoder.scalarFintype

theorem character_count :
    Fintype.card (Module.Dual F2 (UpperVector rows upper)) =
      2 ^ rows (Nodes.height upper) := by
  simpa only [OwnInputReference.UpperVector, HierarchicalArrays.Block,
    Module.finrank_fin_fun] using
    (OutputAnnihilator.card_dual (K := UpperVector rows upper))

theorem coset_probability_lower_oai
    (ρ h₀ : ℝ) (hρ : 0 < ρ) (hh₀ : 0 < h₀)
    (hrep : RecursiveSamplerBias.RepetitionsBalanced repeats)
    (hslice : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ h₀ / 2)
    (hlist : (7 / 8 : ℝ) ^ repeats (Nodes.height upper) ≤ (ρ * h₀ / 4) ^ 2 / 2)
    (hexcluded : 1 / (2 : ℝ) ^ Module.finrank F2 W < ρ / 8)
    (Q : Submodule F2 (Module.Dual F2 (UpperSpace slots upper)))
    (hsize : h₀ ≤ 1 / (2 : ℝ) ^ Module.finrank F2 (Q →ₗ[F2] W))
    (target : Q →ₗ[F2] W) (z : Module.Dual F2 (UpperSpace slots upper))
    (offset : UpperVector rows upper)
    (hmatch : ρ ≤ RightDecoderWitness.conditionalMatch slots rows upper lower W a
      repeats cut labeling input Q target z offset) :
    (ρ * h₀ / 4) ^ 2 / (2 * (2 : ℝ) ^ rows (Nodes.height upper)) ≤
      (RightDecoder.law slots rows upper lower W a repeats cut labeling input (ρ * h₀ / 4)).probability
        (fun decoded => decide (decoded - z ∈ Q)) := by
  have hthreshold : 0 < ρ * h₀ / 4 := div_pos (mul_pos hρ hh₀) (by norm_num)
  obtain ⟨σ, hσ, Φ, hΦ, herror⟩ :=
    RightDecoderWitness.exists_heavy_error_coset slots rows upper lower W a
      repeats cut labeling input ρ h₀ hρ hh₀ hrep hslice hexcluded Q hsize target z offset hmatch
  have h := RightDecoder.coset_lower_of_balanced slots rows upper lower W a
    repeats cut labeling input (ρ * h₀ / 4) hrep hthreshold hlist Q z
    ⟨σ, Φ, hΦ, hσ, herror⟩
  simpa only [character_count rows upper, Nat.cast_pow, Nat.cast_ofNat] using h

end
end PerfectCompleteness.RightDecoderAffineSuccess

end

end OAI
end

theorem solution : type_of% @OAI.PerfectCompleteness.RightDecoderAffineSuccess.coset_probability_lower_oai := @OAI.PerfectCompleteness.RightDecoderAffineSuccess.coset_probability_lower_oai
