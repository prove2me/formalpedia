-- Prove2me | solution 1 for OAI.CubicEisenstein.schlafliBesselK_cubic_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T20:49:45.742636+00:00
-- url     : https://prove2.me/submissions/5efbf59c-a972-4e5e-9652-619f27f23589

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_GaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_Reciprocity_KubotaCharacter
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_ResidualFourierBounds
import Theorems.Thm_OAI_CubicEisenstein_schlafliBesselK_cubic_real
import Theorems.Thm_OAI_CubicEisenstein_cubicBesselIntegral_lower

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
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical
open Filter MeasureTheory
open scoped BigOperators Classical Topology
namespace OAI.CubicEisenstein
theorem _root_.solution (x : ℝ) (hx : 0<x) :
    cubicBesselLowerConstant*Real.exp (-9*x/4)≤(schlafliBesselK (1/3:ℂ) x).re := by
  rw [schlafliBesselK_cubic_real x hx,Complex.ofReal_re]
  have hp := mul_le_mul_of_nonneg_left (cubicBesselIntegral_lower x hx)
    (show 0≤(1/2:ℝ)*(x/2)^(-(1:ℝ)/3) by positivity)
  have hnorm : (x/2)^(-(1:ℝ)/3)=(1/2:ℝ)^(-(1:ℝ)/3)*x^(-(1:ℝ)/3) := by
    rw [show x/2=(1/2:ℝ)*x by ring,Real.mul_rpow (by norm_num) hx.le]
  have htwo : (2*x)^(-(2:ℝ)/3)=(2:ℝ)^(-(2:ℝ)/3)*x^(-(2:ℝ)/3) :=
    Real.mul_rpow (by norm_num) hx.le
  have hxp : x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3)=1 := by
    calc
      _ = x^(-(1:ℝ)/3)*x^(1:ℝ)*x^(-(2:ℝ)/3) := by rw [Real.rpow_one]
      _ = x^((-(1:ℝ)/3+1)+(-(2:ℝ)/3)) := by rw [←Real.rpow_add hx,←Real.rpow_add hx]
      _ = 1 := by norm_num
  have he : (1/2:ℝ)*(x/2)^(-(1:ℝ)/3)*(x*((2*x)^(-(2:ℝ)/3)*Real.exp (-9*x/4)))=
      cubicBesselLowerConstant*Real.exp (-9*x/4) := by
    rw [hnorm,htwo]
    calc
      _ = cubicBesselLowerConstant*(x^(-(1:ℝ)/3)*x*x^(-(2:ℝ)/3))*Real.exp (-9*x/4) := by
        unfold cubicBesselLowerConstant
        ring
      _ = _ := by rw [hxp,mul_one]
  rwa [he] at hp
end OAI.CubicEisenstein
