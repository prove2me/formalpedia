-- Prove2me | solution 1 for OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction_difference
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T08:17:37.402345+00:00
-- url     : https://prove2.me/submissions/318a4149-d554-477e-a667-9dd747f84bd8

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
import Theorems.Thm_OAI_PerfectCompleteness_HeterogeneousAdviceFamily_J_probability_ge
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalAdviceExperiment_lower_I_implies_prediction
import Theorems.Thm_OAI_PerfectCompleteness_HierarchicalAdviceFamily_reference_I_mass_ge

section
-- module Solutions.OAIQ252_PC.UniqueGames_Foundations_MixtureLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

/-! Exact finite total variation and its event-probability bound. -/

namespace UniqueGamesTheorem.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Ω : Type*} [Fintype Ω]

theorem totalVariation_comm (μ ν : FiniteDistribution Ω) :
    μ.totalVariation ν = ν.totalVariation μ := by
  unfold totalVariation
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  exact abs_sub_comm _ _

/-- A one-sided event difference is bounded by half the total absolute mass
difference. Normalization is used; the full absolute-mass sum would lose a
factor of two needed in the repetition argument. -/
theorem probability_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    μ.probability event - ν.probability event ≤ μ.totalVariation ν := by
  have pointwise (x : Ω) :
      2 * ((if event x then μ.weight x else 0) -
        (if event x then ν.weight x else 0)) ≤
      |μ.weight x - ν.weight x| + (μ.weight x - ν.weight x) := by
    have h₁ := le_abs_self (μ.weight x - ν.weight x)
    have h₂ := neg_le_abs (μ.weight x - ν.weight x)
    cases event x <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  have summed := Finset.sum_le_sum (s := Finset.univ) fun x _ => pointwise x
  simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    μ.normalized, ν.normalized, sub_self, add_zero] at summed
  unfold probability totalVariation
  linarith

theorem probability_abs_sub_le_totalVariation (μ ν : FiniteDistribution Ω)
    (event : Ω → Bool) :
    |μ.probability event - ν.probability event| ≤ μ.totalVariation ν := by
  apply abs_le.mpr
  constructor
  · have h := ν.probability_sub_le_totalVariation μ event
    rw [totalVariation_comm] at h
    linarith
  · exact μ.probability_sub_le_totalVariation ν event

end
end UniqueGamesTheorem.Foundations.Games.FiniteDistribution

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
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DualQuotientRowsLemmas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.SmallBiasSlice

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games
open PerfectCompleteness.SmallBias

noncomputable section

variable {Ω I : Type*} [Fintype Ω] [Fintype I] [DecidableEq I]

theorem expectation_const_mul (μ : FiniteDistribution Ω) (c : ℝ) (g : Ω → ℝ) :
    μ.expectation (fun x => c * g x) = c * μ.expectation g := by
  unfold FiniteDistribution.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring


end

end PerfectCompleteness.SmallBiasSlice

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_TupleIndexEmitterLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalKeyShape.dummyAssignmentFintype _root_.OAI.PerfectCompleteness.CanonicalKeyShape.inputFintype _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Appendix.A5Passage.pairFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
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

omit [Fintype P] in
theorem useful_iff (μ : FiniteDistribution Ω) (p : Ω → P) (L : Ω → Bool)
    (κ : ℝ) (z : P) :
    useful μ p L κ z = true ↔
      0 < marginalMass μ p z ∧ κ ≤ conditionalLower μ p L z := by
  simp only [useful, decide_eq_true_eq]

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



namespace PerfectCompleteness.UsefulAdvice

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open UsefulMark

noncomputable section

variable {Ω P : Type*} [Fintype Ω] [Fintype P]

theorem marked_probability_eq_sum (μ : FiniteDistribution Ω) (p : Ω → P)
    (event : P → Bool) :
    μ.probability (fun x => event (p x)) =
      ∑ z, if event z then marginalMass μ p z else 0 := by
  simpa only [lowerFiberMass, marginalMass, Bool.true_and] using
    probability_mark_eq_sum μ p (fun _ => true) event

omit [Fintype P] in
theorem useful_fiber_lower (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (κ : ℝ) (z : P) (hz : useful μ p L κ z = true) :
    κ * marginalMass μ p z ≤ lowerFiberMass μ p L z := by
  obtain ⟨hpos, hratio⟩ := (useful_iff μ p L κ z).mp hz
  exact (le_div_iff₀ hpos).mp hratio

theorem marked_lower_bound (μ : FiniteDistribution Ω) (p : Ω → P)
    (L : Ω → Bool) (κ : ℝ) (event : P → Bool)
    (hmarked : ∀ z, event z = true → useful μ p L κ z = true) :
    κ * μ.probability (fun x => event (p x)) ≤
      μ.probability (fun x => L x && event (p x)) := by
  rw [marked_probability_eq_sum μ p event,
    probability_mark_eq_sum μ p L event, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : event z = true
  · simpa only [ite_eq_left hz] using useful_fiber_lower μ p L κ z (hmarked z hz)
  · simp only [ite_eq_right hz, mul_zero, le_refl]

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

theorem independent_advice_lower_bound (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution A) (p : Ω → P) (L : Ω → Bool) (κ : ℝ)
    (event : P × A → Bool)
    (hmarked : ∀ z a, event (z, a) = true → useful μ p L κ z = true) :
    κ * (μ.product ν).probability (fun x => event (p x.1, x.2)) ≤
      (μ.product ν).probability (fun x => L x.1 && event (p x.1, x.2)) := by
  rw [product_probability_advice_first, product_probability_advice_first,
    ← SmallBiasSlice.expectation_const_mul]
  apply PerfectCompleteness.SmallBias.expectation_mono
  intro a
  exact marked_lower_bound μ p L κ (fun z => event (z, a)) (fun z => hmarked z a)

theorem independent_advice_predicts (μ : FiniteDistribution Ω)
    (ν : FiniteDistribution A) (p : Ω → P) (L : Ω → Bool) (κ : ℝ)
    (event : P × A → Bool) (prediction : Ω × A → Bool)
    (hmarked : ∀ z a, event (z, a) = true → useful μ p L κ z = true)
    (hpredict : ∀ x a, L x = true → event (p x, a) = true →
      prediction (x, a) = true) :
    κ * (μ.product ν).probability (fun x => event (p x.1, x.2)) ≤
      (μ.product ν).probability prediction := by
  apply (independent_advice_lower_bound μ ν p L κ event hmarked).trans
  apply FiniteDistribution.probability_mono
  rintro ⟨x, a⟩ h
  have hh := Bool.and_eq_true_iff.mp h
  exact hpredict x a hh.1 hh.2

end
end PerfectCompleteness.UsefulAdvice



namespace PerfectCompleteness.PredictionDifference

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem scalar_bound (κ α q₀ v h pI pJ pMatch : ℝ)
    (hκ : 0 ≤ κ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hq₀ : 0 ≤ q₀)
    (hv : 0 ≤ v) (hsmall : v ≤ α * q₀ / 16) (hmass : q₀ ≤ h)
    (hI : α * h - v ≤ pI) (hJ : pJ ≤ h + v)
    (hpredict : κ * pI ≤ pMatch) :
    κ * α * q₀ / 4 ≤ pMatch - (κ * α / 4) * pJ := by
  have hκα : 0 ≤ κ * α := mul_nonneg hκ hα
  have hρ : 0 ≤ κ * α / 4 := div_nonneg hκα (by norm_num)
  have hρκ : κ * α / 4 ≤ κ := by
    have h := mul_le_mul_of_nonneg_left hα1 hκ
    nlinarith
  have hp := (mul_le_mul_of_nonneg_left hI hκ).trans hpredict
  have hj := mul_le_mul_of_nonneg_left hJ hρ
  have hc : 0 ≤ κ * α - κ * α / 4 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hmass hc
  have he := mul_le_mul_of_nonneg_left hsmall hκ
  have he' := mul_le_mul_of_nonneg_right hρκ hv
  have hmain := mul_nonneg hκα hq₀
  nlinarith

variable {Ω Γ O : Type*} [Fintype Ω] [Fintype Γ] [Fintype O]

theorem of_observed_variation
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (observe : Ω → O) (referenceObserve : Γ → O)
    (I J : O → Bool) (prediction : Ω → Bool)
    (κ α q₀ v : ℝ) (hκ : 0 ≤ κ) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hq₀ : 0 ≤ q₀) (hv : 0 ≤ v) (hsmall : v ≤ α * q₀ / 16)
    (hvariation : (μ.pushforward observe).totalVariation
      (ν.pushforward referenceObserve) ≤ v)
    (hmass : q₀ ≤ ν.probability (fun x => J (referenceObserve x)))
    (hdensity : α * ν.probability (fun x => J (referenceObserve x)) ≤
      ν.probability (fun x => I (referenceObserve x)))
    (hpredict : κ * μ.probability (fun x => I (observe x)) ≤ μ.probability prediction) :
    κ * α * q₀ / 4 ≤ μ.probability prediction -
      (κ * α / 4) * μ.probability (fun x => J (observe x)) := by
  have hi := (μ.pushforward observe).probability_abs_sub_le_totalVariation
    (ν.pushforward referenceObserve) I
  have hj := (μ.pushforward observe).probability_abs_sub_le_totalVariation
    (ν.pushforward referenceObserve) J
  rw [FiniteDistribution.probability_pushforward,
    FiniteDistribution.probability_pushforward] at hi hj
  have hi' := (abs_le.mp (hi.trans hvariation)).1
  have hj' := (abs_le.mp (hj.trans hvariation)).2
  apply scalar_bound κ α q₀ v (ν.probability (fun x => J (referenceObserve x)))
    (μ.probability (fun x => I (observe x)))
    (μ.probability (fun x => J (observe x))) (μ.probability prediction)
    hκ hα hα1 hq₀ hv hsmall hmass
  · linarith
  · linarith
  · exact hpredict

end
end PerfectCompleteness.PredictionDifference

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_DependentPredictionDifferenceLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.HierarchicalUsefulness.coarseFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.DependentPredictionDifference

noncomputable section

open scoped Classical
open UniqueGamesTheorem.Foundations.Games

variable {O : Type*}

variable [Fintype O] {Ω P A : O → Type*}
  [∀ o, Fintype (Ω o)] [∀ o, Fintype (P o)] [∀ o, Fintype (A o)]

theorem original_usefulness_predicts
    (outer : FiniteDistribution O)
    (original : ∀ o, FiniteDistribution (Ω o))
    (advice : ∀ o, FiniteDistribution (A o))
    (p : ∀ o, Ω o → P o) (lower : ∀ o, Ω o → Bool)
    (I : Observation P A → Bool) (prediction : Sample Ω A → Bool) (κ : ℝ)
    (hmarked : ∀ o z a, I ⟨o, (z, a)⟩ = true →
      UsefulMark.useful (original o) (p o) (lower o) κ z = true)
    (hprediction : ∀ o x a, lower o x = true → I ⟨o, (p o x, a)⟩ = true →
      prediction ⟨o, (x, a)⟩ = true) :
    κ * (law outer original advice).probability (fun x => I (observe p x)) ≤
      (law outer original advice).probability prediction := by
  unfold law
  rw [CompletionSoundness.sigmaLaw_probability, CompletionSoundness.sigmaLaw_probability,
    ← SmallBiasSlice.expectation_const_mul]
  apply SmallBias.expectation_mono
  intro o
  exact UsefulAdvice.independent_advice_predicts (original o) (advice o) (p o) (lower o) κ
    (fun z => I ⟨o, z⟩) (fun x => prediction ⟨o, x⟩) (hmarked o) (hprediction o)

theorem of_original_usefulness {Γ : Type*} [Fintype Γ]
    (outer : FiniteDistribution O)
    (original : ∀ o, FiniteDistribution (Ω o))
    (advice : ∀ o, FiniteDistribution (A o))
    (reference : FiniteDistribution Γ)
    (p : ∀ o, Ω o → P o) (referenceObserve : Γ → Observation P A)
    (lower : ∀ o, Ω o → Bool)
    (I J : Observation P A → Bool) (prediction : Sample Ω A → Bool)
    (κ ρ q₀ v : ℝ) (hκ : 0 ≤ κ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq₀ : 0 ≤ q₀) (hv : 0 ≤ v) (hsmall : v ≤ ρ * q₀ / 16)
    (hmarked : ∀ o z a, I ⟨o, (z, a)⟩ = true →
      UsefulMark.useful (original o) (p o) (lower o) κ z = true)
    (hprediction : ∀ o x a, lower o x = true → I ⟨o, (p o x, a)⟩ = true →
      prediction ⟨o, (x, a)⟩ = true)
    (hvariation : ((law outer original advice).pushforward (observe p)).totalVariation
      (reference.pushforward referenceObserve) ≤ v)
    (hmass : q₀ ≤ reference.probability (fun x => J (referenceObserve x)))
    (hdensity : ρ * reference.probability (fun x => J (referenceObserve x)) ≤
      reference.probability (fun x => I (referenceObserve x))) :
    κ * ρ * q₀ / 4 ≤ (law outer original advice).probability prediction -
      (κ * ρ / 4) * (law outer original advice).probability (fun x => J (observe p x)) := by
  apply PredictionDifference.of_observed_variation
    (law outer original advice) reference (observe p) referenceObserve I J prediction
    κ ρ q₀ v hκ hρ hρ1 hq₀ hv hsmall hvariation hmass hdensity
  exact original_usefulness_predicts outer original advice p lower I prediction κ
    hmarked hprediction

end
end PerfectCompleteness.DependentPredictionDifference


end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalFrozenTablesLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightLabel_nonempty _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.keyLabel_nonempty _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawNonempty _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawNonempty _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFinite _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedFintype _root_.OAI.PerfectCompleteness.CutSamplerRefinement.refinedNonempty _root_.OAI.PerfectCompleteness.CutTerminalSplit.childSquareFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFinite _root_.OAI.PerfectCompleteness.OwnInputReference.exteriorFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.OwnInputReference.scalarSampleFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorDecidableEq _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFinite _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorFintype _root_.OAI.PerfectCompleteness.ProjectedCardinality.factorNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.childSquareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.drawSpaceNonempty _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryDrawFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.tapeNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.blockNonempty _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayExteriorLaw.exteriorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.tapeNonempty _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementFintype _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.complementNonempty _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorFintype _root_.OAI.PerfectCompleteness.WholeCutGrouping.exteriorNonempty _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeFintype _root_.OAI.PerfectCompleteness.WholeCutSampler.tapeNonempty
attribute [-simp] _root_.OAI.PerfectCompleteness.BoundedListSampling.jointLaw_weight _root_.OAI.PerfectCompleteness.BoundedListSampling.listLaw_empty_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_weight _root_.OAI.PerfectCompleteness.BucketSampler.tapeLaw_zero_width_weight _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.labelEmbedding_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.partIndex_transportFine _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportCoarse_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningEncoding.transportFine_val _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.labelIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.partIndex_transportLabel _root_.OAI.PerfectCompleteness.CanonicalCoarseningErasure.transportLabel_val _root_.OAI.PerfectCompleteness.CanonicalDirections.choiceAt_toCanonical _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_apply _root_.OAI.PerfectCompleteness.CanonicalDirections.tupleEquiv_symm_apply _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_map _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.family_size _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalL_val _root_.OAI.PerfectCompleteness.CanonicalLocalCompletion.legalR_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_left _root_.OAI.PerfectCompleteness.CanonicalNamedGame.completed_right _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.leftKeys_length _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_accepts _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rename_occurrences _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightEmbedding_at_val _root_.OAI.PerfectCompleteness.CanonicalNamedGame.rightKeys_length _root_.OAI.PerfectCompleteness.CanonicalPartialTable.leftEmbedding_input _root_.OAI.PerfectCompleteness.ChildBlockProjection.arraysPullback_apply _root_.OAI.PerfectCompleteness.ChildBlockProjection.squarePullback_apply _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.equiv_symm_calls _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_arrays _root_.OAI.PerfectCompleteness.ChildCallNumbering.pullback_calls _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.number_unnumber _root_.OAI.PerfectCompleteness.ChildCallNumberingLaws.unnumber_number _root_.OAI.PerfectCompleteness.ChildUnmarkedSpace.childMap_apply _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairAgrees_read _root_.OAI.PerfectCompleteness.CleanRecordDecoderInput.event_observe _root_.OAI.PerfectCompleteness.CleanRecordObservation.event_observe _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_knownBuckets _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_lowerQuotient _root_.OAI.PerfectCompleteness.CleanRightDecoder.input_otherArrays _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_apply _root_.OAI.PerfectCompleteness.CompletedSignedLaw.completedEquiv_source _root_.OAI.PerfectCompleteness.CutCallExtension.split_assemble _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_arrays _root_.OAI.PerfectCompleteness.CutChildGrouping.assemble_calls _root_.OAI.PerfectCompleteness.CutProjectionAssembly.castProjection_heq _root_.OAI.PerfectCompleteness.CutSamplerReplay.retainedSum_apply _root_.OAI.PerfectCompleteness.CutSlotAssembly.fill_at_cut _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_exterior_apply _root_.OAI.PerfectCompleteness.CutTerminalSplit.splitTape_terminal_apply _root_.OAI.PerfectCompleteness.DecoderContraction.descendantSquareEmbedding_apply _root_.OAI.PerfectCompleteness.DecoderRankSplit.highAgrees_eq_true _root_.OAI.PerfectCompleteness.DecoderSourcePullback.upperTarget_apply _root_.OAI.PerfectCompleteness.DescriptorKeyTemplate.actualSlot_erase _root_.OAI.PerfectCompleteness.DescriptorProjectionMachine.outputWords_length _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_apply _root_.OAI.PerfectCompleteness.DesignatedLeaves.equiv_symm_apply _root_.OAI.PerfectCompleteness.FilledUniformSampler.childrenEquiv_apply _root_.OAI.PerfectCompleteness.FiniteListSampling.uniformList_weight_mem _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_map _root_.OAI.PerfectCompleteness.FinitePreliminaryCompletion.family_size _root_.OAI.PerfectCompleteness.HierarchicalLeftDecoder.squareEmbedding_apply _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_background _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.input_testedMatrix _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.testedMatrix_update _root_.OAI.PerfectCompleteness.HierarchicalLowerMatrixInput.updateBackground_selected _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_call _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complement_merge _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_arrays _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_directRow _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_otherCall _root_.OAI.PerfectCompleteness.LowerCutCallSplit.merge_split _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_complement _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitAssembled_rows _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.splitEquiv_symm_apply _root_.OAI.PerfectCompleteness.LowerCutCallSplit.split_merge _root_.OAI.PerfectCompleteness.LowerCutRows.selectRows_apply _root_.OAI.PerfectCompleteness.LowerCutScalar.reconstruct_refl _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_ordinary _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_root _root_.OAI.PerfectCompleteness.MetadataFreeTape.tapeEquiv_selected _root_.OAI.PerfectCompleteness.NativeLeafAlphabet.castAssignment_rfl _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_ordinary _root_.OAI.PerfectCompleteness.OriginalBelowCut.below_selected _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_array _root_.OAI.PerfectCompleteness.OriginalChildBlocks.rawMap_call _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_other _root_.OAI.PerfectCompleteness.OriginalChildScalarAssembly.stepSquareMap_self _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_other _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareComponent_self _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_exterior_apply _root_.OAI.PerfectCompleteness.OriginalTerminalSplit.splitExpanded_terminal_apply _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_lower _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_other _root_.OAI.PerfectCompleteness.OwnInputCanonicalQuery.assemble_upper _root_.OAI.PerfectCompleteness.ProjectedCleanRate.projectionFlag_true _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginalSquare_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.intoOriginal_apply _root_.OAI.PerfectCompleteness.ProjectedNodeEmbedding.nativePullback_apply _root_.OAI.PerfectCompleteness.RecursiveSampler.combine_zero _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_refl _root_.OAI.PerfectCompleteness.RecursiveSampler.evaluate_zeroTape _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childBilinear_apply _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childProduct_val _root_.OAI.PerfectCompleteness.RecursiveSamplerBiasAlgebra.childSquareLift_val _root_.OAI.PerfectCompleteness.RightDecoderDescendant.form_apply _root_.OAI.PerfectCompleteness.RightDecoderDescendant.squareEmbedding_apply _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.replace_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_assemble_step _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_refl _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_replace _root_.OAI.PerfectCompleteness.SelectedArrayReplacement.selectedRows_step _root_.OAI.PerfectCompleteness.SignedScheduleIndex.atIndex_signs _root_.OAI.PerfectCompleteness.SignedTupleBodyMachine.bodySigns_prepared _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceIDs_tuple _root_.OAI.PerfectCompleteness.SignedTupleSemantics.sourceVariables_tuple _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeNative_tagged _root_.OAI.PerfectCompleteness.SourceChildKernel.decodeProjected_tagged _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_raw _root_.OAI.PerfectCompleteness.SourceChildKernelJoint.groupEquiv_sources _root_.OAI.PerfectCompleteness.SourceQuestionOrder.questionToTuple_tupleToQuestion _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_length _root_.OAI.PerfectCompleteness.SourceQuestionOrder.sourceOrder_toFinset _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_length _root_.OAI.PerfectCompleteness.SourceVisitOrder.visitOrder_toFinset _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_fst _root_.OAI.PerfectCompleteness.WholeArrayBucketsLaw.split_snd _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_nodePath _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.selectedNode_succ _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_height _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_refl _root_.OAI.PerfectCompleteness.WholeArrayInteriorExterior.upperNode_step _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.childrenAt_selected _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_ordinary _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_refl _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_root _root_.OAI.PerfectCompleteness.WholeArraySampler.evaluate_selected _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_refl _root_.OAI.PerfectCompleteness.WholeArraySubtreeSplit.extract_step _root_.OAI.PerfectCompleteness.WholeCutExteriorTransport.scalarEquiv_apply _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeCutSubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_refl _root_.OAI.PerfectCompleteness.WholeReplaySubtree.extract_step _root_.OAI.PerfectCompleteness.WholeReplaySubtree.knownBucketsAtNode_apply _root_.OAI.PerfectCompleteness.WholeReplaySubtree.rootBuckets_step _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringGlobalConfiguration.boolList_mpr_eq _root_.OAI.UniqueGamesTheorem.Foundations.Games.FiniteDistribution.pushforward_id
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI



namespace PerfectCompleteness.HierarchicalUsefulness

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

noncomputable section

variable {branch rows : Nat → Nat} {n t : Nat}
  (slots : RecursiveSpaces.Slots branch n → Fin t → MixedSupport.Slot)
  (upper : Nodes branch n) (lowerLevel : Nat)

variable {Ω : Type*} [Fintype Ω]
  (original : FiniteDistribution Ω) (arrays : Ω → Arrays slots rows)
  (lower : Ω → Bool) (κ : ℝ)

variable (σ : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t))

theorem table_isSome (background : HierarchicalMatrixTable.Background (rows := rows) slots upper)
    (X : HierarchicalFrozenTables.QuotientMatrix slots upper lowerLevel background) :
    (table slots upper lowerLevel original arrays lower κ σ background X).isSome =
      mark slots upper lowerLevel original arrays lower κ ⟨background, X⟩ := by
  unfold table HierarchicalFrozenTables.table RepresentativeMatrixTable.partialTable
  cases h : mark slots upper lowerLevel original arrays lower κ ⟨background, X⟩ <;>
    simp [h]

end
end PerfectCompleteness.HierarchicalUsefulness



end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalPrediction
attribute [-instance] _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.OwnInputReference.frequencyFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalPrediction

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter (linearMapFintype)

attribute [local instance] linearMapFintype

section Selection

variable {E K Y : Type*} [AddCommGroup E] [Module F2 E]
  [AddCommGroup K] [Module F2 K] [FiniteDimensional F2 E]
  [FiniteDimensional F2 K] [Fintype E] [Fintype K] [Fintype Y]

omit [FiniteDimensional F2 E] [FiniteDimensional F2 K] [Fintype Y] in
theorem selectedValue_of_I (f : (E →ₗ[F2] K) → Option Y) (r : Nat) (ρ : ℝ)
    (A : ManyGoodRows.RowMap K r) (X : E →ₗ[F2] K)
    (hI : GoodAdviceEvents.I f r ρ (A, X) = true) :
    ∃ y, selectedValue f r ρ A X = some y ∧ f X = some y := by
  unfold GoodAdviceEvents.I GoodAdviceEvents.selectedAgreement at hI
  by_cases h : ManyGoodRows.GoodRow f r ρ A (A.comp X)
  · simp only [dite_eq_left h, decide_eq_true_eq] at hI
    exact ⟨(ManyGoodRows.selectWitness f r ρ A (A.comp X) h).value,
      by simp only [selectedValue, dite_eq_left h], hI.2⟩
  · simp only [dite_eq_right h, Bool.false_eq_true] at hI

end Selection

end
end PerfectCompleteness.HierarchicalPrediction

end OAI
end

section
-- module Solutions.OAIQ252_PC.PerfectCompleteness_Foundations_HierarchicalAdviceExperimentLemmas
attribute [-instance] _root_.OAI.PerfectCompleteness.CanonicalGame.leftVertex_finite _root_.OAI.PerfectCompleteness.CanonicalGame.rightVertex_finite _root_.OAI.PerfectCompleteness.CanonicalKeys.KeyLabel_finite _root_.OAI.PerfectCompleteness.CanonicalPartialTable.inputFintype _root_.OAI.PerfectCompleteness.ChildBlockCardinality.rawFintype _root_.OAI.PerfectCompleteness.ChildBlockProjection.liftedRangeFintype _root_.OAI.PerfectCompleteness.ChildCallNumbering.rawFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.leftAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.pairFintype _root_.OAI.PerfectCompleteness.CleanDecoderPairLaw.rightAnswerFintype _root_.OAI.PerfectCompleteness.CleanDecoderRate.seedFintype _root_.OAI.PerfectCompleteness.CleanDecoderSeedLaw.seedFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.lowerAnswerFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.ownFintype _root_.OAI.PerfectCompleteness.CleanLeftDecoder.upperAnswerFintype _root_.OAI.PerfectCompleteness.CleanPhysicalDecoderLaw.answersFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.assembledFintype _root_.OAI.PerfectCompleteness.CutChildGrouping.childFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.rightOutputFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.taggedRightFintype _root_.OAI.PerfectCompleteness.FixedQueryCodec.testIndexFintype _root_.OAI.PerfectCompleteness.HierarchicalAllDecoderTables.inputFintype _root_.OAI.PerfectCompleteness.LowerCutCallSplit.complementFintype _root_.OAI.PerfectCompleteness.MetadataFreeSampler.inputFintype _root_.OAI.PerfectCompleteness.MetadataFreeTape.inputFintype _root_.OAI.PerfectCompleteness.OriginalChildScalars.squareFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.callTapesFintype _root_.OAI.PerfectCompleteness.RecursiveSampler.childFamilyFinite _root_.OAI.PerfectCompleteness.RecursiveSampler.ordinaryTapeFintype _root_.OAI.PerfectCompleteness.SourceAnswerEquiv.rightDomainDecidableEq _root_.OAI.PerfectCompleteness.SourceChildKernel.blockFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.rawFintype _root_.OAI.PerfectCompleteness.SourceChildKernel.sampleFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.factorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restFactorFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.restTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayHiddenLaw.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArrayPositiveSplit.scalarTapeFintype _root_.OAI.PerfectCompleteness.WholeArraySampler.spaceFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderFamily.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineExpanderTable.alphabetFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeDecidableEq _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.MachineRegularOwnerCleanup.tapeFintype _root_.OAI.UniqueGamesTheorem.Foundations.Complexity.PoweringMachineGlobal.labelFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace PerfectCompleteness.HierarchicalAdviceExperiment

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Fourier.MatrixLevelBridge
open UniqueGamesTheorem.Appendix.RankLevelFilter

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {Ω : Type*} [Fintype Ω]
  (S : Experiment branch rows n t Ω)

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceExperiment.backgroundFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceExperiment.inputFintype
local instance inputFiniteDimensional :
    (b : Background S) → FiniteDimensional F2 (Input S b) :=
  fun _ => inferInstance

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceExperiment.valueFintype
theorem I_implies_mark (κ : ℝ) (r : Nat) (ρ : ℝ) (z : Coarse S) (A : Advice S r)
    (hI : I S κ r ρ (z, A) = true) :
    UsefulMark.useful S.original (coarse S) (lowerEvent S) κ z = true := by
  obtain ⟨y, _, hy⟩ := HierarchicalPrediction.selectedValue_of_I
    (table S κ z.1) r ρ A z.2 hI
  have hsome := congrArg Option.isSome hy
  change (HierarchicalUsefulness.table S.slots S.upper S.lowerLevel S.original S.arrays
    (lowerEvent S) κ S.strategy z.1 z.2).isSome = true at hsome
  rw [HierarchicalUsefulness.table_isSome] at hsome
  exact hsome

end
end PerfectCompleteness.HierarchicalAdviceExperiment


namespace PerfectCompleteness.HierarchicalAdviceFamily

noncomputable section

open scoped Classical
open TreeSourceSpaces HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Appendix.RankLevelFilter
open UniqueGamesTheorem.Fourier.MatrixLevelBridge

attribute [local instance] linearMapFintype

variable {branch rows : Nat → Nat} {n t : Nat} {O : Type*} [Fintype O]
  {Ω : O → Type*} [∀ o, Fintype (Ω o)]
  (S : (o : O) → HierarchicalAdviceExperiment.Experiment branch rows n t (Ω o))

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.backgroundFiberFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.inputFintype
local instance inputFiniteDimensional (b : Background S) : FiniteDimensional F2 (Input S b) :=
  HierarchicalAdviceExperiment.inputFiniteDimensional (S b.1) b.2

attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.valueFintype
attribute [local instance] OAI.PerfectCompleteness.HierarchicalAdviceFamily.coarseFintype
omit [Fintype O] in
theorem reference_J (κ : ℝ) (r : Nat) (ρ : ℝ) (x : ReferenceSample S r) :
    J S κ r ρ (referenceObserve S r x) =
      HeterogeneousAdviceFamily.J (table S κ) r ρ x := rfl

theorem reference_J_mass_ge (κ : ℝ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))
    (ℓ : Nat) (hdim : ∀ o, rows (Nodes.height (S o).upper) ≤ ℓ)
    (r : Nat) (ρ η : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ (backgroundLaw S outer backgrounds).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (table S κ b))) :
    (η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2 ≤
      (referenceLaw S outer backgrounds r).probability
        (fun x => J S κ r ρ (referenceObserve S r x)) := by
  let : ∀ b : Background S, Nontrivial (Row S b) := fun b => by
    let : Nonempty (Fin (rows (Nodes.height (S b.1).upper))) := ⟨⟨0, hrows b.1⟩⟩
    exact inferInstance
  have hdim' (b : Background S) : Module.finrank F2 (Row S b) ≤ ℓ := by
    simpa only [Row, Block, Module.finrank_fin_fun] using hdim b.1
  have hevent : (fun x => J S κ r ρ (referenceObserve S r x)) =
      HeterogeneousAdviceFamily.J (table S κ) r ρ := by
    funext x
    exact reference_J S κ r ρ x
  rw [hevent]
  exact HeterogeneousAdviceFamily.J_probability_ge
    (backgroundLaw S outer backgrounds) (table S κ) r ℓ hdim' ρ η hη hρ hρ1 hconstants hmean

theorem prediction_difference_oai (κ : ℝ) (hκ : 0 ≤ κ) (outer : FiniteDistribution O)
    (backgrounds : (o : O) → FiniteDistribution (HierarchicalAdviceExperiment.Background (S o)))
    (hrows : ∀ o, 0 < rows (Nodes.height (S o).upper))
    (ℓ : Nat) (hdim : ∀ o, rows (Nodes.height (S o).upper) ≤ ℓ)
    (r : Nat) (ρ η v : ℝ) (hη : 0 < η) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hconstants : levelCutoffConstant r ρ + node (r + 1) < η / 2)
    (hmean : 2 * η ≤ (backgroundLaw S outer backgrounds).expectation
      (fun b => PartialTableInverse.nonzeroAgreement (table S κ b)))
    (hv : 0 ≤ v) (hsmall : v ≤ ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) / 16)
    (hvariation : ((originalLaw S outer r).pushforward (observe S r)).totalVariation
      ((referenceLaw S outer backgrounds r).pushforward (referenceObserve S r)) ≤ v) :
    κ * ρ * ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) / 4 ≤
      (originalLaw S outer r).probability (prediction S κ r ρ) -
      (κ * ρ / 4) * (originalLaw S outer r).probability
        (fun x => J S κ r ρ (observe S r x)) := by
  apply DependentPredictionDifference.of_original_usefulness outer
    (fun o => (S o).original) (fun o => HierarchicalAdviceExperiment.adviceLaw (S o) r)
    (referenceLaw S outer backgrounds r) (fun o => HierarchicalAdviceExperiment.coarse (S o))
    (referenceObserve S r) (fun o => HierarchicalAdviceExperiment.lowerEvent (S o))
    (I S κ r ρ) (J S κ r ρ) (prediction S κ r ρ)
    κ ρ ((η ^ 2 / 4) / ((2 : ℝ) ^ (r * ℓ)) ^ 2) v
    hκ hρ.le hρ1.le (by positivity) hv hsmall
  · intro o z A hI
    exact HierarchicalAdviceExperiment.I_implies_mark (S o) κ r ρ z A hI
  · intro o x A hL hI
    exact HierarchicalAdviceExperiment.lower_I_implies_prediction (S o) κ r ρ x A hL hI
  · exact hvariation
  · exact reference_J_mass_ge S κ outer backgrounds hrows ℓ hdim r ρ η
      hη hρ hρ1 hconstants hmean
  · exact reference_I_mass_ge S κ outer backgrounds r ρ

end
end PerfectCompleteness.HierarchicalAdviceFamily


end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction_difference_oai.{u_1, u_2} := @OAI.PerfectCompleteness.HierarchicalAdviceFamily.prediction_difference_oai.{u_1, u_2}
