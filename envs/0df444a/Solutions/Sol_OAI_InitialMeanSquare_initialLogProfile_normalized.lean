-- Prove2me | solution 1 for OAI.InitialMeanSquare.initialLogProfile_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T12:04:25.644609+00:00
-- url     : https://prove2.me/submissions/f3a6e9e3-b9d9-4e10-912b-8a92b52d9c40

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectedBranches
import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
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
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
namespace OAI.InitialMeanSquare
theorem _root_.solution {ι : Type*} (p : ι → O)
    (hp : ∀ i, p i ≠ 0) (S : Finset ι) (Z : ℝ) (hZ : 0 < Z)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    normalizedColumn p (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S =
      (Real.sqrt Z : ℂ)⁻¹*W (primeProductNorm p S/Z) := by
  let n := ‖eisEmbedding (∏ i ∈ S,p i)‖
  have hn : 0 < n := norm_pos_iff.mpr
    (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
  have hpos : 0 < n^2/Z := div_pos (sq_pos_of_pos hn) hZ
  have hexp : Real.exp (Real.log (n^2/Z)/2)=n/Real.sqrt Z := by
    rw [←JointLogSeparation.sqrt_exp_half, Real.exp_log hpos,
      Real.sqrt_div (sq_nonneg n), Real.sqrt_sq hn.le]
  change ((Real.exp (Real.log (n^2/Z)/2) : ℂ)*W (Real.exp (Real.log (n^2/Z)))) /
    (n : ℂ) = (Real.sqrt Z : ℂ)⁻¹*W (n^2/Z)
  rw [hexp, Real.exp_log hpos, Complex.ofReal_div]
  have hn0 : (n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  have hsz : (Real.sqrt Z : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hZ).ne'
  field_simp
end OAI.InitialMeanSquare
