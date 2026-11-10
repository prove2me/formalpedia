-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.cutoffRescaleCoefficient_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T06:04:13.688916+00:00
-- url     : https://prove2.me/submissions/9446393c-ea22-4792-8d0f-d5e24d70bade

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
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (C η r q : ℝ) (hr : 0<r) (hq : 0<q) :
    cutoffRescaleCoefficient C η r q=C*r^(1-η)*q^(2+η) := by
  rw [cutoffRescaleCoefficient,Real.div_rpow hr.le hq.le,
    Real.rpow_sub hr,Real.rpow_one,Real.rpow_add hq,Real.rpow_two]
  have hrp : r^η≠0 := (Real.rpow_pos_of_pos hr η).ne'
  have hqp : q^η≠0 := (Real.rpow_pos_of_pos hq η).ne'
  field_simp
end OAI.CanonicalQuadraticSieve
