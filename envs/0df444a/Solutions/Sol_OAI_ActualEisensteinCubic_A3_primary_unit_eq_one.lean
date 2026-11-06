-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.A3_primary_unit_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:57:42.917839+00:00
-- url     : https://prove2.me/submissions/fc3961d4-a95a-45e5-9063-a50dff9b53bc

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_ActualEisensteinCubic_lambda_not_dvd_two


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
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
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
open OAI.ActualEisensteinCubic
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (x : O) (hx : IsUnit x)
    (hprimary : lambda ^ 2 ∣ x - 1) : x = 1 := by
  let v : Oˣ := hx.unit
  have hv : (v : O) = x := hx.unit_spec
  have hvprimary : lambda ^ 2 ∣ (v : O) - 1 := by
    simpa only [hv] using hprimary
  have hunit : v = 1 ∨ v = -1 := by
    apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent
      (IsCyclotomicExtension.zeta_spec 3 ℚ K) v
    refine ⟨(1 : ℤ), ?_⟩
    simpa only [lambda, omega, Int.cast_one] using hvprimary
  rcases hunit with h1 | hneg
  · calc
      x = (v : O) := hv.symm
      _ = 1 := by rw [h1]; rfl
  · have heq : (v : O) - 1 = -(2 : O) := by
      rw [hneg]
      norm_num
    rw [heq] at hvprimary
    have htwo : lambda ^ 2 ∣ (2 : O) := (dvd_neg).mp hvprimary
    exact False.elim (lambda_not_dvd_two
      ((dvd_pow_self lambda (by decide)).trans htwo))
end OAI.ActualEisensteinCubic
