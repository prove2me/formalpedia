-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.normFiberExpSum_le_of_prefix_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:14:48.622833+00:00
-- url     : https://prove2.me/submissions/01bbd946-a1bf-4a92-ba8c-7ad4b443d8d7

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Theorems.Thm_OAI_ShortDraftHeckeBridge_geometric_rpow_moment_bound
import Theorems.Thm_OAI_ShortDraftHeckeBridge_tsum_eq_one_sub_mul_tsum_prefix
import Theorems.Thm_OAI_ShortDraftHeckeBridge_exp_inv_geometric_gap
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftHeckeBridge_normFiberExpSum_summable
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
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
namespace NormSplitArithmetic
end NormSplitArithmetic
namespace NormFiberCRT
end NormFiberCRT
namespace NormFiberMult
end NormFiberMult
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open Filter Asymptotics
namespace ShortDraftHeckeBridge
private theorem summable_add_one_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr)
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
open Filter Asymptotics
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    {q r₀ : ℕ} [NeZero q] [NeZero r₀]
    (χ : DirichletCharacter ℂ q) (ψ : DirichletCharacter ℂ r₀)
    (weight : Ideal O → ℂ)
    (hcoeff : ∀ n : ℕ, n ≠ 0 → normFiberCoeff weight n = pairInverseCoeff χ ψ n)
    (ha0 : normFiberCoeff weight 0 = 0)
    (σ C : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hC : 0 ≤ C)
    (hprefix : ∀ n : ℕ,
      ‖prefixCoeff (normFiberCoeff weight) n‖ ≤ C * (((n : ℝ) + 1) ^ σ))
    (D : ℝ) (hD : 1 ≤ D) :
    ‖normFiberExpSum weight D⁻¹‖ ≤ 3 * C * D ^ σ := by
  let a : ℕ → ℂ := normFiberCoeff weight
  let r : ℝ := Real.exp (-D⁻¹)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have ht : 0 < D⁻¹ := inv_pos.mpr hDpos
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)
  have hpow (n : ℕ) : Real.exp (-(n : ℝ) * D⁻¹) = r ^ n := by
    dsimp [r]
    convert Real.exp_nat_mul (-D⁻¹) n using 1 ; ring_nf
  have hf : Summable (fun n : ℕ => a n * (r : ℂ) ^ n) := by
    have h := normFiberExpSum_summable χ ψ weight hcoeff ha0 D⁻¹ ht
    simpa only [a, hpow, Complex.ofReal_pow] using h
  have hS : normFiberExpSum weight D⁻¹ =
      ∑' n : ℕ, a n * (r : ℂ) ^ n := by
    unfold normFiberExpSum
    apply tsum_congr
    intro n
    simp only [a, hpow, Complex.ofReal_pow]
  have habel := tsum_eq_one_sub_mul_tsum_prefix a r hr0 hr1 hf
  have hlin : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) :=
    summable_add_one_mul_geometric hr0 hr1
  have hmoment : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ σ) * r ^ n) := by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (Real.rpow_nonneg (by positivity) σ) (pow_nonneg hr0 _))
      (fun n => ?_) hlin
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_self_of_one_le (by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith) hσ1) (pow_nonneg hr0 _)
  have hdom : Summable (fun n : ℕ => C * ((((n : ℝ) + 1) ^ σ) * r ^ n)) :=
    hmoment.mul_left C
  have hpoint (n : ℕ) :
      ‖prefixCoeff a n * (r : ℂ) ^ n‖ ≤
        C * ((((n : ℝ) + 1) ^ σ) * r ^ n) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0]
    have h := mul_le_mul_of_nonneg_right (hprefix n) (pow_nonneg hr0 n)
    simpa only [mul_assoc] using h
  have hnorm : Summable (fun n : ℕ => ‖prefixCoeff a n * (r : ℂ) ^ n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint hdom
  have hgap : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
  have hmomentBound := geometric_rpow_moment_bound σ D r hσ0 hσ1 hD hr0 hr1
    (exp_inv_geometric_gap D hD)
  calc
    ‖normFiberExpSum weight D⁻¹‖ =
        ‖(1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n)‖ := by
          rw [hS, habel]
    _ = (1 - r) * ‖∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n‖ := by
      have hreal : (1 - (r : ℂ)) = ((1 - r : ℝ) : ℂ) := by push_cast; ring
      rw [norm_mul, hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hgap]
    _ ≤ (1 - r) * (∑' n : ℕ, ‖prefixCoeff a n * (r : ℂ) ^ n‖) :=
      mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) hgap
    _ ≤ (1 - r) * (∑' n : ℕ,
          C * ((((n : ℝ) + 1) ^ σ) * r ^ n)) :=
      mul_le_mul_of_nonneg_left (Summable.tsum_le_tsum hpoint hnorm hdom) hgap
    _ = C * ((1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n)) := by
      rw [tsum_mul_left]
      ring
    _ ≤ C * (3 * D ^ σ) := mul_le_mul_of_nonneg_left hmomentBound hC
    _ = 3 * C * D ^ σ := by ring
end OAI.ShortDraftHeckeBridge
