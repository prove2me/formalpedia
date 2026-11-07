-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.pairInverseCoeff_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:49:32.39121+00:00
-- url     : https://prove2.me/submissions/0c9f6668-a16a-42cc-83cd-b474f7ca338d

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LocalNonvanishing
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_NormFiberMellin
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace ShortDraftLocal
end ShortDraftLocal
open MulChar AddChar
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftHeckeBridge
private theorem mobius_char_coeff_norm_le_one
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖χ n * (ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have hχ : ‖χ n‖ ≤ 1 := χ.norm_le_one _
  have hμ : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
    (norm_nonneg ((ArithmeticFunction.moebius n : ℂ))),
    mul_nonneg (sub_nonneg.mpr hμ) (norm_nonneg (χ n))]
end ShortDraftHeckeBridge
end
end OAI
end

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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r : ℕ} [NeZero q] [NeZero r]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r)
    (n : ℕ) : ‖pairInverseCoeff χ ψ n‖ ≤ (n : ℝ) := by
  rw [pairInverseCoeff, LSeries.convolution_def]
  have hcard : (n.divisorsAntidiagonal.card : ℝ) ≤ n := by
    rw [← Nat.map_div_right_divisors, Finset.card_map]
    exact_mod_cast Nat.card_divisors_le_self n
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal,
        (χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)) *
        (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))‖ ≤
      ∑ p ∈ n.divisorsAntidiagonal,
        ‖(χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)) *
        (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ n.divisorsAntidiagonal, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      have hχ := mobius_char_coeff_norm_le_one χ p.1
      have hψ := mobius_char_coeff_norm_le_one ψ p.2
      nlinarith [mul_nonneg (sub_nonneg.mpr hχ)
        (norm_nonneg (ψ p.2 * (ArithmeticFunction.moebius p.2 : ℂ))),
        mul_nonneg (sub_nonneg.mpr hψ)
          (norm_nonneg (χ p.1 * (ArithmeticFunction.moebius p.1 : ℂ)))]
    _ = (n.divisorsAntidiagonal.card : ℝ) := by simp
    _ ≤ n := hcard
end OAI.ShortDraftHeckeBridge
