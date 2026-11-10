-- Prove2me | solution 1 for OAI.CompletedGauss.short_cube_scales
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T08:26:51.367229+00:00
-- url     : https://prove2.me/submissions/b9d37b2d-3361-4054-aa73-d06d9cf2f1ee

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_TransformedColumns
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_ProductColumns
import Theorems.Thm_OAI_CompletedGauss_short_cube_scale_algebra

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
open scoped BigOperators Classical
open OAI.CompletedGauss
open ActualEisensteinCubic CanonicalQuadraticSieve
namespace OAI.CompletedGauss
theorem _root_.solution (Z K R X F h : ℝ)
    (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hh : 1≤h) (hhZ : h≤Z^(1/1000:ℝ))
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ))) :
    1≤X/h^3 ∧ K^2*R*F*h^3/X≤K := by
  have hZ0 : 0<Z := by linarith
  have hz : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have he : (Z^(1/1000:ℝ))^25=Z^(1/40:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le]
    norm_num
  apply short_cube_scale_algebra _ K R X F h hz hK hR hF hFZ hh hhZ
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ0.le (1/40:ℝ))
  have hp : Z^(-(1/40:ℝ))*Z^(1/40:ℝ)=1 := by
    rw [←Real.rpow_add hZ0]
    norm_num
  calc
    _ ≤ X*F*Z^(-(1/40:ℝ))*Z^(1/40:ℝ) := hm
    _ = X*F := by rw [mul_assoc (X*F),hp,mul_one]
end OAI.CompletedGauss
