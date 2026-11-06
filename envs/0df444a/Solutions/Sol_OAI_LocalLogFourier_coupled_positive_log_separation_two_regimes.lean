-- Prove2me | solution 1 for OAI.LocalLogFourier.coupled_positive_log_separation_two_regimes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:07:32.063219+00:00
-- url     : https://prove2.me/submissions/ed7bddfc-a0fd-4f45-a194-807feff66b2a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_euler_two_regime_bound
import Theorems.Thm_OAI_LocalLogFourier_coupled_positive_log_separation_uniform

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
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
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
open OAI.LocalLogFourier
namespace OAI.LocalLogFourier
theorem _root_.solution
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F : ℝ → ℂ) (a M : ι → ℝ)
    (hM : ∀ j, 0 ≤ M j)
    (hWwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (A J : ℕ) (Csmall Clarge : ℝ)
    (hCs : 0 ≤ Csmall) (hCl : 0 ≤ Clarge)
    (hsmall : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x → x ≤ 1 →
        ‖eulerDeriv F i x‖ ≤ Csmall)
    (hlarge : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 1 ≤ x →
        x ^ A * ‖eulerDeriv F i x‖ ≤ Clarge) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∃ b : ℝ → ℂ,
        (∀ y : ι → ℝ,
          (∏ j : ι, W j (y j)) *
            F (R * Real.exp (∑ j : ι, a j * y j)) =
          ∫ t : ℝ,
            (∏ j : ι, W j (y j) *
              FourierBridge.logPhase t (a j * y j)) * b t) ∧
        (1 + R) ^ A *
          (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤ C := by
  apply coupled_positive_log_separation_uniform W F a M
    hM hWwindow hFpos A J
    ((2 : ℝ) ^ A * (Csmall + Clarge))
    (by positivity)
  intro i hi x hx
  exact euler_two_regime_bound F A
    (J + (volume : Measure ℝ).integrablePower)
    Csmall Clarge hCs hCl hsmall hlarge i hi x hx
end OAI.LocalLogFourier
