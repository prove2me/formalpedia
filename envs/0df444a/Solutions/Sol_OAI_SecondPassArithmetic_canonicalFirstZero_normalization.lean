-- Prove2me | solution 1 for OAI.SecondPassArithmetic.canonicalFirstZero_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:21:38.95868+00:00
-- url     : https://prove2.me/submissions/d0f9f0a0-8333-486a-9863-3e062dc29ee8

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_UnitRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CuspHeight
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_BarrierPotential

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
namespace OAI.SecondPassArithmetic
theorem _root_.solution (C Γ X F K B Z ε : ℝ)
    (hC : 0≤C) (hX : 0<X) (hF : 0≤F) (hK : 0≤K) (hB : 1≤B)
    (hrow : K≤(X*F)*Z^(-((1:ℝ)/40))) :
    B*(C*(Real.exp 1*B)^(1+ε)*(X/B^3)*F*Γ^2*K)≤
      (C*(Real.exp 1)^(1+ε))*B^ε*Γ^2*(X*F)^2*Z^(-((1:ℝ)/40)) := by
  have hB0 : 0<B := zero_lt_one.trans_le hB
  have hc : 0≤C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F) := by
    positivity
  calc
    _ = (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K/B := by
      rw [Real.mul_rpow (Real.exp_pos _).le hB0.le,Real.rpow_add hB0,Real.rpow_one]
      field_simp

    _ ≤ (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*K :=
      div_le_self (mul_nonneg hc hK) hB
    _ ≤ (C*(Real.exp 1)^(1+ε)*B^ε*Γ^2*(X*F))*((X*F)*Z^(-((1:ℝ)/40))) :=
      mul_le_mul_of_nonneg_left hrow hc
    _ = _ := by ring
end OAI.SecondPassArithmetic
