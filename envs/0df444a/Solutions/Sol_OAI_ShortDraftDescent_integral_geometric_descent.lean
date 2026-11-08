-- Prove2me | solution 1 for OAI.ShortDraftDescent.integral_geometric_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:05:09.477176+00:00
-- url     : https://prove2.me/submissions/47c43f30-e0b6-4440-aaed-660f609fd1ef

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspIntegration
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_MaskedPrincipalBounds

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open OAI.ShortDraftDescent
open MeasureTheory Filter
namespace OAI.ShortDraftDescent
theorem _root_.solution
    {Node Parameter : Type*} [MeasurableSpace Parameter]
    (rank : Node → ℕ) (energy mass terminal : Node → ℝ)
    (left right : Node → Parameter → Node)
    (measure : Node → Measure Parameter) (weight : Node → Parameter → ℝ)
    (hweight : ∀ x, ∀ᵐ t ∂measure x, 0 ≤ weight x t)
    (hintegrable : ∀ x, Integrable (fun t => weight x t *
      Real.sqrt (mass (left x t)) * Real.sqrt (mass (right x t))) (measure x))
    (hterminal : ∀ x, rank x = 0 → energy x ≤ mass x)
    (hchildren : ∀ x, rank x ≠ 0 → ∀ᵐ t ∂measure x,
      rank (left x t) < rank x ∧ rank (right x t) < rank x)
    (hstep : ∀ x, rank x ≠ 0 → energy x ≤ terminal x +
      ∫ t, weight x t * Real.sqrt (energy (left x t)) * Real.sqrt (energy (right x t)) ∂measure x)
    (hbudget : ∀ x, rank x ≠ 0 → terminal x +
      (∫ t, weight x t * Real.sqrt (mass (left x t)) * Real.sqrt (mass (right x t)) ∂measure x) ≤ mass x) :
    ∀ x, energy x ≤ mass x := by
  have h : ∀ n : ℕ, ∀ x, rank x = n → energy x ≤ mass x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x hx
      by_cases hn : n = 0
      · exact hterminal x (hx.trans hn)
      have hx0 : rank x ≠ 0 := by omega
      have hmono : (∫ t, weight x t * Real.sqrt (energy (left x t)) *
          Real.sqrt (energy (right x t)) ∂measure x) ≤
          ∫ t, weight x t * Real.sqrt (mass (left x t)) *
          Real.sqrt (mass (right x t)) ∂measure x := by
        refine integral_mono_of_nonneg ?_ (hintegrable x) ?_
        · filter_upwards [hweight x] with t ht
          exact mul_nonneg (mul_nonneg ht (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
        · filter_upwards [hweight x, hchildren x hx0] with t ht hr
          have hl := ih (rank (left x t)) (by omega) (left x t) rfl
          have hh := ih (rank (right x t)) (by omega) (right x t) rfl
          exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) ht)
            (Real.sqrt_le_sqrt hh) (Real.sqrt_nonneg _)
            (mul_nonneg ht (Real.sqrt_nonneg _))
      exact (hstep x hx0).trans ((add_le_add le_rfl hmono).trans (hbudget x hx0))
  intro x
  exact h (rank x) x rfl
end OAI.ShortDraftDescent
