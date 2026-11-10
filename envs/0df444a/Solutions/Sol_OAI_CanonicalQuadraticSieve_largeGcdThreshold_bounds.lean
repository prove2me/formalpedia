-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.largeGcdThreshold_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:04:51.527282+00:00
-- url     : https://prove2.me/submissions/b3eb509d-e041-4566-abb3-08592e3d1f19

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GlobalScales
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_AnnularLifting

set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (α N : ℝ) (hα1 : 1≤α) (hα2 : α≤2) (hN : 4≤N) :
    1≤largeGcdThreshold α N ∧ largeGcdThreshold α N≤N/2 := by
  have hα : 0<α := by linarith
  have hN0 : 0<N := by linarith
  have ha : 0≤1-1/α := by
    have hi : 1/α≤1 := (div_le_one hα).mpr hα1
    linarith
  have hb : 1-1/α≤(1/2:ℝ) := by
    have hi : (1/2:ℝ)≤1/α := (le_div_iff₀ hα).mpr (by linarith)
    linarith
  refine ⟨Real.one_le_rpow (by linarith) ha,?_⟩
  calc
    largeGcdThreshold α N ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
    _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
    _ ≤ N/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
end OAI.CanonicalQuadraticSieve
