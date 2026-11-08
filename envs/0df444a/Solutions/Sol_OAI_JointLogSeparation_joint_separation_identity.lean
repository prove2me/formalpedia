-- Prove2me | solution 1 for OAI.JointLogSeparation.joint_separation_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:27:02.829829+00:00
-- url     : https://prove2.me/submissions/b015b55c-12af-4da8-896e-41f052532af2

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_PrimitiveRows
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_PrincipalTruncation
import Theorems.Thm_OAI_JointLogSeparation_schwartz_phase_inversion
import Theorems.Thm_OAI_JointLogSeparation_product_three_integrals

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
open scoped BigOperators Classical SchwartzMap
open OAI.JointLogSeparation
open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform
open FourierBridge FirstPassCubeLabels
namespace OAI.JointLogSeparation
theorem _root_.solution
    (A₁ A₂ : 𝓢(ℝ, ℂ)) (b : 𝓢(ℝ, ℂ)) (P F : ℂ) (s₁ s₂ s₃ : ℝ)
    (hr : P * F = ∫ t : ℝ, P * logPhase t s₃ * b t) :
    P * A₁ s₁ * A₂ s₂ * F =
      ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        P * logPhase t₁ s₁ * logPhase t₂ s₂ * logPhase t₃ s₃ *
          ((𝓕 A₁) t₁ * (𝓕 A₂) t₂ * b t₃) := by
  calc
    _ = A₁ s₁ * A₂ s₂ * (P * F) := by ring
    _ = (∫ t : ℝ, logPhase t s₁ * (𝓕 A₁) t) *
        (∫ t : ℝ, logPhase t s₂ * (𝓕 A₂) t) *
        (∫ t : ℝ, P * logPhase t s₃ * b t) := by
      rw [← schwartz_phase_inversion, ← schwartz_phase_inversion, ← hr]
    _ = ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
        (logPhase t₁ s₁ * (𝓕 A₁) t₁) * (logPhase t₂ s₂ * (𝓕 A₂) t₂) *
          (P * logPhase t₃ s₃ * b t₃) := by
      exact product_three_integrals
        (fun t : ℝ => logPhase t s₁ * (𝓕 A₁) t)
        (fun t : ℝ => logPhase t s₂ * (𝓕 A₂) t)
        (fun t : ℝ => P * logPhase t s₃ * b t)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with t₁
      apply integral_congr_ae
      filter_upwards [] with t₂
      apply integral_congr_ae
      filter_upwards [] with t₃
      ring
end OAI.JointLogSeparation
