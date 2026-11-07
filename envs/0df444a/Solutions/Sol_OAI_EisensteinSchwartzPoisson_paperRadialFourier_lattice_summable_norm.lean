-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:35:47.846201+00:00
-- url     : https://prove2.me/submissions/12667eb6-9291-4192-a322-9203d0ea0d29

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_source_weighted_bound
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_eisenstein_cauchy_summable
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_polynomial_tail_majorant

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
open OAI.EisensteinSchwartzPoisson
open ConcreteTraceCRT ActualEisensteinCubic
open scoped SchwartzMap
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun h : O => ‖paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2)‖) := by
  obtain ⟨s, C, hC, hb⟩ := paperRadialFourier_source_weighted_bound 2
  let B := C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let D := (min 1 K) ^ 2 * (1 + (0 : ℝ)) ^ (0 : ℕ)
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _
    (eisenstein_cauchy_summable.mul_left (B / D))
  intro h
  exact polynomial_tail_majorant 0 K 0 _ B _ hK (by norm_num)
    (sq_nonneg _) (norm_nonneg _) (by positivity) (hb W _ (by positivity))
end OAI.EisensteinSchwartzPoisson
