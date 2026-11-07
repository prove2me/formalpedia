-- Prove2me | solution 1 for OAI.FirstPassCubeLabels.cubePairRow_radial_poisson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:31:39.62917+00:00
-- url     : https://prove2.me/submissions/86238ecf-5e10-48b0-a80e-c13f39737a59

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_FirstPassCubeLabels_cubeConductorExponent_ne_zero
import Theorems.Thm_OAI_FirstPassCubeLabels_cubeConductorExponent_lt_six
import Theorems.Thm_OAI_FirstPassCubeLabels_cubePairRow_conductor_selection
import Theorems.Thm_OAI_ActualEisensteinCubic_canonical_masked_radial_poisson_collected


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
open scoped BigOperators Classical
open OAI.FirstPassCubeLabels
open ActualEisensteinCubic
open scoped SchwartzMap ContDiff
open ConcreteTraceCRT
open EisensteinSchwartzPoisson (paperRadialFourier)
namespace OAI.FirstPassCubeLabels
theorem _root_.solution {κ : Type*} [DecidableEq κ]
    (P : κ → Ideal O) [∀ j, (P j).IsMaximal] (hinj : Function.Injective P)
    (hg : ∀ j, lambda ∉ P j) (hc : ∀ j, ringChar (O ⧸ P j) ≠ 2)
    (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hcover : ∀ j ∈ B, 0 < v₁ j + v₂ j + bit (ε₁ j) + bit (ε₂ j))
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, cubePairRow P hg B v₁ v₂ ε₁ ε₂ z *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      cubePairPoissonKernel P hinj hg B v₁ v₂ ε₁ ε₂ W scale := by
  simp_rw [cubePairRow_conductor_selection P hg B v₁ v₂ ε₁ ε₂ hcover]
  exact canonical_masked_radial_poisson_collected P hinj
    (cubePrincipalSupport B v₁ v₂ ε₁ ε₂)
    (fun j : cubeConductorSupport B v₁ v₂ ε₁ ε₂ => P j.val)
    (cubeConductorPrimes_pairwise_coprime P hinj B v₁ v₂ ε₁ ε₂)
    (fun j => hg j.val) (fun j => hc j.val)
    (fun j => (conductorExponent (parity (v₁ j.val + v₂ j.val)) (ε₁ j.val) (ε₂ j.val)).val)
    (cubeConductorExponent_ne_zero B v₁ v₂ ε₁ ε₂)
    (cubeConductorExponent_lt_six B v₁ v₂ ε₁ ε₂) W scale hscale
end OAI.FirstPassCubeLabels
