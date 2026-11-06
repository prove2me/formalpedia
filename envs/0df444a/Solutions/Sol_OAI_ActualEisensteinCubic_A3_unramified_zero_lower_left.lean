-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.A3_unramified_zero_lower_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:58:34.983193+00:00
-- url     : https://prove2.me/submissions/98f814e6-2ec9-4a25-9a5c-d0c04285b70d

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_ActualEisensteinCubic_A3_primary_unit_eq_one

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
theorem _root_.solution
    (a b c : O) (hdet : a * 0 - b * c = 1)
    (hcprimary : lambda ^ 2 ∣ c - 1) :
    c = 1 ∧ -b = 1 := by
  have hprod : (-b) * c = 1 := by linear_combination hdet
  have hcunit : IsUnit c :=
    IsUnit.of_mul_eq_one (-b) (by simpa only [mul_comm] using hprod)
  have hc1 := A3_primary_unit_eq_one c hcunit hcprimary
  refine ⟨hc1, ?_⟩
  simpa only [hc1, mul_one] using hprod
end OAI.ActualEisensteinCubic
