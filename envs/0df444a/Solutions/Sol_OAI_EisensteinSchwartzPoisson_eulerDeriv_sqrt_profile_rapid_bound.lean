-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.eulerDeriv_sqrt_profile_rapid_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:33:01.298523+00:00
-- url     : https://prove2.me/submissions/aa2dd1b0-ab4a-4e62-8a08-7b9f96d69f2a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_eulerDeriv_sqrt_profile
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_sqrt_profile_rapid_bound

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
open OAI.EisensteinSchwartzPoisson
open MeasureTheory
open scoped SchwartzMap ContDiff
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (g : 𝓢(ℝ, ℂ)) (A j : ℕ)
    (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (fun s => g (Real.sqrt s)) j x‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0
          ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g) +
        SchwartzMap.seminorm ℝ (2 * A) 0
          ((halfEulerCLM : 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ))^[j] g)) := by
  rw [eulerDeriv_sqrt_profile g j x hx]
  exact sqrt_profile_rapid_bound _ A x hx
end OAI.EisensteinSchwartzPoisson
