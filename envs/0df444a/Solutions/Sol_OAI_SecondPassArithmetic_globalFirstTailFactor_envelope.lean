-- Prove2me | solution 1 for OAI.SecondPassArithmetic.globalFirstTailFactor_envelope
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:35:26.545636+00:00
-- url     : https://prove2.me/submissions/aad2b39a-7fd3-4211-a3ae-f0bf52db7b98

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningBounds

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
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.SecondPassArithmetic
namespace OAI.SecondPassArithmetic
theorem _root_.solution (K ell B F U H : ℝ) (N : ℕ)
    (hK : 0≤K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F)
    (hU : 1≤U) (hH : 0≤H) (hKU : K≤U) (hiell : ell⁻¹≤U) :
    globalFirstTailFactor K ell B F U H N≤4096*U^20/(1+H)^N := by
  have hBi : B⁻¹≤1 := inv_le_one_of_one_le₀ hB
  have hFi : F⁻¹≤1 := inv_le_one_of_one_le₀ hF
  have hratio : K*U^2/(ell^2*B^2*F^2)≤U^5 := by
    calc
      _ = K*U^2*(ell⁻¹)^2*(B⁻¹)^2*(F⁻¹)^2 := by field_simp
      _ ≤ U*U^2*U^2*1^2*1^2 := by gcongr
      _ = _ := by ring
  have hone : 1+U≤2*U := by linarith
  have hinner : 1+(1+U)^3*(K*U^2/(ell^2*B^2*F^2))≤16*U^8 := by
    calc
      _ ≤ 1+(2*U)^3*U^5 := by gcongr
      _ = 1+8*U^8 := by ring
      _ ≤ _ := by have hh : 1≤U^8 := one_le_pow₀ hU; linarith
  unfold globalFirstTailFactor
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ (2*U)^4*(16*U^8)^2 := by gcongr
    _ = _ := by ring
end OAI.SecondPassArithmetic
