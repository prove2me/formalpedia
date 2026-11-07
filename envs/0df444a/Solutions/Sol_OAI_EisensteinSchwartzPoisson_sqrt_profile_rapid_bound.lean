-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.sqrt_profile_rapid_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:28:59.087195+00:00
-- url     : https://prove2.me/submissions/5ce05291-f570-4210-801d-503468118d1d

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier

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
theorem _root_.solution (g : 𝓢(ℝ, ℂ)) (A : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ A * ‖g (Real.sqrt x)‖ ≤
      2 ^ A * (SchwartzMap.seminorm ℝ 0 0 g +
        SchwartzMap.seminorm ℝ (2 * A) 0 g) := by
  have hsmall := SchwartzMap.norm_le_seminorm ℝ g (Real.sqrt x)
  have hlarge := SchwartzMap.norm_pow_mul_le_seminorm ℝ g (2 * A) (Real.sqrt x)
  have hsqrt : ‖Real.sqrt x‖ ^ (2 * A) = x ^ A := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
      pow_mul, Real.sq_sqrt hx]
  rw [hsqrt] at hlarge
  have hs0 : 0 ≤ SchwartzMap.seminorm ℝ 0 0 g := by positivity
  have hsA : 0 ≤ SchwartzMap.seminorm ℝ (2 * A) 0 g := by positivity
  by_cases hx1 : x ≤ 1
  · have hp : (1 + x) ^ A ≤ (2 : ℝ) ^ A := by gcongr; linarith
    calc
      _ ≤ 2 ^ A * ‖g (Real.sqrt x)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ 2 ^ A * SchwartzMap.seminorm ℝ 0 0 g := by gcongr
      _ ≤ _ := by gcongr; linarith
  · have hp : (1 + x) ^ A ≤ (2 * x) ^ A := by gcongr; linarith
    calc
      _ ≤ (2 * x) ^ A * ‖g (Real.sqrt x)‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ = 2 ^ A * (x ^ A * ‖g (Real.sqrt x)‖) := by rw [mul_pow]; ring
      _ ≤ 2 ^ A * SchwartzMap.seminorm ℝ (2 * A) 0 g := by gcongr
      _ ≤ _ := by gcongr; linarith
end OAI.EisensteinSchwartzPoisson
