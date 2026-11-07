-- Prove2me | solution 1 for OAI.CubicReflectionKernel.paperKernel_euler_vanish_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:50:33.962629+00:00
-- url     : https://prove2.me/submissions/2342c1a0-edb6-4a47-b85a-2036cc526ff8

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_InitialBound
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ReflectedKernel
import Theorems.Thm_OAI_CubicReflectionKernel_paperScale_pos
import Theorems.Thm_OAI_CubicReflectionKernel_paperKernel_euler_eq
import Theorems.Thm_OAI_CubicReflectionKernel_reflectedLogProfile_deriv_vanish

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
open scoped Classical FourierTransform SchwartzMap ContDiff Topology
open MeasureTheory Filter
open OAI.CubicReflectionKernel
namespace OAI.CubicReflectionKernel
theorem _root_.solution (V : ℝ → ℂ) (logSource : SchwartzMap ℝ ℂ)
    (hL : ∀ u, logSource u = V (Real.exp u)) (j : ℕ) :
    Tendsto (LocalLogFourier.eulerDeriv (paperKernel V) j) (𝓝[>] 0) (𝓝 0) := by
  have hd := (reflectedLogProfile_deriv_vanish logSource j).mono_left atBot_le_cocompact
  have hmul : Tendsto (fun x : ℝ => paperScale * x) (𝓝[>] 0) (𝓝[>] 0) := by
    have hm : Tendsto (fun x : ℝ => paperScale * x)
        (comap (fun x : ℝ => paperScale * x) (𝓝[>] 0)) (𝓝[>] 0) := tendsto_comap
    rwa [comap_mulLeft_nhdsGT_zero paperScale_pos] at hm
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hmul
  apply (hd.comp hlog).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (paperKernel_euler_eq V logSource hL j x hx).symm
end OAI.CubicReflectionKernel
