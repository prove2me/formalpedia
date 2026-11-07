-- Prove2me | solution 1 for OAI.EisensteinSchwartzPoisson.compact_paperRadialFourier_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:43:11.074333+00:00
-- url     : https://prove2.me/submissions/6219a269-9992-4592-ad31-5444ffffe89e

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticRadialPoisson
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_RadialFourier
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_contDiffOn
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_paperRadialFourier_euler_bound

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
open MeasureTheory
open scoped SchwartzMap ContDiff
namespace OAI.EisensteinSchwartzPoisson
theorem _root_.solution
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (hWs : ContDiff ℝ ∞ W)
    (A K : ℕ) :
    ContDiffOn ℝ ∞ (paperRadialFourier W) (Set.Ioi 0) ∧
      ∃ CF : ℝ, 0 ≤ CF ∧ ∀ j ≤ K, ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖LocalLogFourier.eulerDeriv (paperRadialFourier W) j x‖ ≤ CF := by
  exact ⟨paperRadialFourier_contDiffOn (hWc.toSchwartzMap hWs),
    paperRadialFourier_euler_bound (hWc.toSchwartzMap hWs) A K⟩
end OAI.EisensteinSchwartzPoisson
