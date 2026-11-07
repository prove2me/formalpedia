-- Prove2me | solution 1 for OAI.TwoPassProfiles.first_dyadic_profile
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:59:42.762468+00:00
-- url     : https://prove2.me/submissions/af2ec8bf-84cd-4827-aa59-447ff7fd79cc

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Theorems.Thm_OAI_TwoPassProfiles_first_profile_exp

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
open OAI.TwoPassProfiles
namespace OAI.TwoPassProfiles
theorem _root_.solution
    (K₀ y₀ d₀ f₀ E₀ t₀ c₀ x₁₀ x₂₀
      k y d f E t c x₁ x₂ : ℝ)
    (hK₀ : K₀ ≠ 0) (hy₀ : y₀ ≠ 0) (hd₀ : d₀ ≠ 0)
    (hf₀ : f₀ ≠ 0) (hE₀ : E₀ ≠ 0) (ht₀ : t₀ ≠ 0)
    (hc₀ : c₀ ≠ 0) (hx₁₀ : x₁₀ ≠ 0) (hx₂₀ : x₂₀ ≠ 0)
    (hk : 0 < k) (hy : 0 < y) (hd : 0 < d)
    (hf : 0 < f) (hE : 0 < E) (ht : 0 < t)
    (hc : 0 < c) (hx₁ : 0 < x₁) (hx₂ : 0 < x₂) :
    (K₀ * k) * (y₀ * y) /
      ((d₀ * d) * (f₀ * f) ^ 2 * (E₀ * E) *
        (t₀ * t) ^ 2 * (c₀ * c) * (x₁₀ * x₁) * (x₂₀ * x₂)) =
      (K₀ * y₀ /
        (d₀ * f₀ ^ 2 * E₀ * t₀ ^ 2 * c₀ * x₁₀ * x₂₀)) *
        Real.exp (∑ j : Fin 9,
          firstCoeff j * firstLogs k y d f E t c x₁ x₂ j) := by
  rw [← first_profile_exp k y d f E t c x₁ x₂
    hk hy hd hf hE ht hc hx₁ hx₂]
  field_simp
end OAI.TwoPassProfiles
