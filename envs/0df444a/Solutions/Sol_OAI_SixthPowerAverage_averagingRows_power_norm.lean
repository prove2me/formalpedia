-- Prove2me | solution 1 for OAI.SixthPowerAverage.averagingRows_power_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T17:40:04.781426+00:00
-- url     : https://prove2.me/submissions/f4f255d1-5d33-4787-989b-d82df30f8ef2

import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_ThetaDensity
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_SixthPowerAverage
import Theorems.Thm_OAI_SixthPowerAverage_mem_averagingRows
import Theorems.Thm_OAI_ActualEisensteinCubic_eisEmbedding_norm_sq_eq_absNorm_span


set_option autoImplicit false
open OAI
noncomputable section
open OAI.SixthPowerAverage
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
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic
open ConcretePrimeRowBridge hiding O
open EisensteinSchwartzPoisson hiding O
open IdealMobiusDivisorSum hiding O
open ConcreteTraceCRT ShortDraftHeckeBridge
open QuadraticInitialBound hiding O
namespace OAI.SixthPowerAverage
theorem _root_.solution (Y : ℝ) (hY : 1≤Y)
    {z : ActualEisensteinCubic.O} (hz : z∈(averagingRows Y).image (fun b=>b^6)) :
    z≠0 ∧ (Ideal.absNorm (Ideal.span {z}):ℝ)≤Y^6 := by
  obtain ⟨b,hb,rfl⟩:=Finset.mem_image.mp hz
  have hh:=(mem_averagingRows (by linarith : (0:ℝ)≤Y)).mp hb
  refine ⟨pow_ne_zero _ hh.1,?_⟩
  rw [←eisEmbedding_norm_sq_eq_absNorm_span,map_pow,norm_pow,
    ←pow_mul,show (6:ℕ)*2=2*6 by omega,pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) hh.2 _
end OAI.SixthPowerAverage
