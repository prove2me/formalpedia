-- Prove2me | solution 1 for OAI.CanonicalCubeSeparation.cube_log_argument
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:19:55.245194+00:00
-- url     : https://prove2.me/submissions/f14850c0-eb91-44f2-b007-527afe2aa2dd

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_SupportBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogSeparation

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
open OAI.CanonicalCubeSeparation
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open FourierBridge JointLogSeparation
namespace OAI.CanonicalCubeSeparation
theorem _root_.solution (B ell n q : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) (hq : 0 < q) :
    Real.exp (Real.log (q/ell) + 3*Real.log (n/B)) = q*n^3/(B^3*ell) := by
  rw [Real.exp_add, Real.exp_log (div_pos hq hell)]
  have he : Real.exp (3*Real.log (n/B)) = (n/B)^3 := by
    rw [show (3:ℝ)*Real.log (n/B) =
      Real.log (n/B)+Real.log (n/B)+Real.log (n/B) by ring]
    rw [Real.exp_add, Real.exp_add, Real.exp_log (div_pos hn hB)]
    ring
  rw [he]
  field_simp
end OAI.CanonicalCubeSeparation
