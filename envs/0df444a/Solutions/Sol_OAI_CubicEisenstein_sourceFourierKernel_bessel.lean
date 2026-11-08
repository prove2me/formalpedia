-- Prove2me | solution 1 for OAI.CubicEisenstein.sourceFourierKernel_bessel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:26:18.767761+00:00
-- url     : https://prove2.me/submissions/30b9316d-fcf2-499e-a4cf-eeb786c709e3

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_Rows
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_HyperbolicSpace
import Theorems.Thm_OAI_CubicEisenstein_sourceFourierKernel_gamma_schlafli

set_option autoImplicit false
open OAI
noncomputable section
open OAI.CubicEisenstein
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
open MeasureTheory Set Filter
open scoped BigOperators Classical
open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace
open MeasureTheory Set Filter
open scoped BigOperators Classical FourierTransform RealInnerProductSpace
namespace OAI.CubicEisenstein
theorem _root_.solution (s freq : ℂ) (hs : 1 < s.re) (hf : freq ≠ 0) :
    sourceFourierKernel s freq =
      (2*Real.pi : ℂ)/Complex.Gamma s *
        (2*Real.pi*‖freq‖ : ℂ)^(s-1) *
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖) := by
  have hg := Complex.Gamma_ne_zero_of_re_pos (show 0 < s.re by linarith)
  have hz : (2*Real.pi*‖freq‖ : ℂ) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hf))
  have hp : (2*Real.pi*‖freq‖ : ℂ)^(s-1) * (2*Real.pi*‖freq‖ : ℂ)^(-(s-1)) = 1 := by
    rw [← Complex.cpow_add _ _ hz, add_neg_cancel, Complex.cpow_zero]
  have hreorder : (2*Real.pi : ℂ)/Complex.Gamma s *
      (2*Real.pi*‖freq‖ : ℂ)^(s-1) * schlafliBesselK (s-1) (4*Real.pi*‖freq‖) =
      ((2*Real.pi : ℂ)*(2*Real.pi*‖freq‖ : ℂ)^(s-1)*
        schlafliBesselK (s-1) (4*Real.pi*‖freq‖))/Complex.Gamma s := by ring
  rw [hreorder]
  apply (eq_div_iff hg).mpr
  rw [sourceFourierKernel_gamma_schlafli s freq hs]
  unfold schlafliBesselK
  push_cast
  have hhalf : (4*(Real.pi : ℂ)*‖freq‖)/2 = 2*Real.pi*‖freq‖ := by ring
  rw [hhalf]
  linear_combination -((Real.pi : ℂ)*schlafliIntegral (s-1) (4*Real.pi*‖freq‖))*hp
end OAI.CubicEisenstein
