-- Prove2me | solution 1 for OAI.TwoPassProfiles.log_dyad_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:57:53.380941+00:00
-- url     : https://prove2.me/submissions/d99cac1e-7956-4729-874f-eb26f9e2e106

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles

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
open OAI.TwoPassProfiles
namespace OAI.TwoPassProfiles
theorem _root_.solution (r : ℝ) (hr₁ : 1 ≤ r) (hr₂ : r ≤ 2) :
    |Real.log r| ≤ Real.log 2 := by
  have hlog0 : 0 ≤ Real.log r := by
    simpa using Real.log_le_log (by positivity : (0 : ℝ) < 1) hr₁
  have hlog2 : Real.log r ≤ Real.log 2 :=
    Real.log_le_log (by linarith) hr₂
  simpa [abs_of_nonneg hlog0] using hlog2
end OAI.TwoPassProfiles
