-- Prove2me | solution 1 for OAI.CubicReflectionKernel.gammaMultiplier_norm_imaginary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:33:12.15209+00:00
-- url     : https://prove2.me/submissions/8b55f464-515c-4833-896c-f195df29b51b

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactWeights
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CoefficientCancellation
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Theorems.Thm_OAI_CubicReflectionKernel_Gamma_vertical_ne_zero
import Theorems.Thm_OAI_CubicReflectionKernel_Gamma_vertical_conj

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
open scoped BigOperators Classical SchwartzMap
open scoped Classical FourierTransform SchwartzMap ContDiff
open MeasureTheory
open OAI.CubicReflectionKernel
namespace OAI.CubicReflectionKernel
theorem _root_.solution (u : ℝ) :
    ‖gammaMultiplier (u * Complex.I)‖ = 1 := by
  have ha := Gamma_vertical_ne_zero (7 / 6) u (by norm_num)
  have hb := Gamma_vertical_ne_zero (5 / 6) u (by norm_num)
  have hca := Gamma_vertical_conj (7 / 6) u
  have hcb := Gamma_vertical_conj (5 / 6) u
  push_cast at ha hb hca hcb
  rw [gammaMultiplier, hca, hcb, norm_div, norm_mul, norm_mul, norm_star, norm_star]
  exact div_self (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))
end OAI.CubicReflectionKernel
