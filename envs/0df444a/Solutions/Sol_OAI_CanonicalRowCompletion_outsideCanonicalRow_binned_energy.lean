-- Prove2me | solution 1 for OAI.CanonicalRowCompletion.outsideCanonicalRow_binned_energy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:25:14.523258+00:00
-- url     : https://prove2.me/submissions/daff73d4-022c-409b-9a1c-72fb59c8bab7

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RadialProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_CanonicalLogEnergy
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_CoordinateLaplacian
import Theorems.Thm_OAI_CanonicalRowCompletion_norm_add_sum_sq_le
import Theorems.Thm_OAI_CanonicalRowCompletion_outsideCanonicalRow_reopened_binned


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
open scoped BigOperators Classical
open OAI.CanonicalRowCompletion
open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic
open CompletedGauss hiding O
open ConcretePrimeRowBridge hiding O columnWeight
open CanonicalQuadraticSieve hiding O
namespace OAI.CanonicalRowCompletion
theorem _root_.solution
    (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0 ≤ b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*X ≤ D) :
    ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 ≤
      2*X*(‖shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀‖^2 +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          ‖outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀)
    (fun j => outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀)
  rw [← outsideCanonicalRow_reopened_binned S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD] at hs
  have hn : ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 =
      X*‖(Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  convert mul_le_mul_of_nonneg_left hs hX.le using 1 <;> first | rfl | ring
end OAI.CanonicalRowCompletion
