-- Prove2me | solution 1 for OAI.CanonicalCubeSeparation.cube_half_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:20:32.759872+00:00
-- url     : https://prove2.me/submissions/b99bd00d-1935-477e-b590-e88ad134159f

import Definitions.Def_OAI_NumberTheory_DirichletL_RowCompletion_SupportBounds
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_ReopeningSeparation
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LogSeparation
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_sqrt_exp_half
import Theorems.Thm_OAI_JointLogSeparation_sqrt_exp_half


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
theorem _root_.solution (B ell n : ℝ) (hB : 0 < B) (hell : 0 < ell)
    (hn : 0 < n) :
    (Real.sqrt (B^3*ell))⁻¹ * Real.sqrt n =
      (B*Real.sqrt ell)⁻¹ * Real.exp (Real.log (n/B)/2) := by
  have hb0 := (Real.sqrt_pos.mpr hB).ne'
  have he0 := (Real.sqrt_pos.mpr hell).ne'
  have hs : Real.sqrt (B^3*ell) = B*Real.sqrt B*Real.sqrt ell := by
    rw [show B^3*ell=B^2*(B*ell) by ring,
      Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB.le, Real.sqrt_mul hB.le]
    ring
  have hnexp : Real.exp (Real.log (n/B)/2) = Real.sqrt n/Real.sqrt B := by
    rw [← sqrt_exp_half, Real.exp_log (div_pos hn hB), Real.sqrt_div hn.le]
  rw [hs, hnexp]
  field_simp
end OAI.CanonicalCubeSeparation
