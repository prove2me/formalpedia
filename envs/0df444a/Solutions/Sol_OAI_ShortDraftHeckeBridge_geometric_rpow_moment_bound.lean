-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.geometric_rpow_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:26.594869+00:00
-- url     : https://prove2.me/submissions/2092c7ef-57d1-42ac-966c-fd3f7bdbb073

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
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
private theorem rpow_le_one_add_of_exponent_Icc (x σ : ℝ)
    (hx : 0 ≤ x) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) : x ^ σ ≤ 1 + x := by
  by_cases hx1 : x ≤ 1
  · have h := Real.rpow_le_one hx hx1 hσ0
    linarith
  · have h := Real.rpow_le_self_of_one_le (le_of_not_ge hx1) hσ1
    linarith
private theorem tsum_add_one_mul_geometric {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ((n : ℝ) + 1) * r ^ n) = 1 / (1 - r) ^ 2 := by
  have hr : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  simpa only [Nat.choose_one_right, Nat.cast_add, Nat.cast_one] using
    (tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hr)
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
    (σ D r : ℝ) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hD : 1 ≤ D) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hscale : 1 / (D * (1 - r)) ≤ 2) :
    (1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n) ≤
      3 * D ^ σ := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hDpow : 0 ≤ D ^ σ := (Real.rpow_pos_of_pos hDpos σ).le
  have hrpow : ∀ n : ℕ,
      (((n : ℝ) + 1) ^ σ) * r ^ n ≤
      D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n)) := by
    intro n
    have hn : 0 ≤ ((n : ℝ) + 1) / D := by positivity
    have heq : D * (((n : ℝ) + 1) / D) = (n : ℝ) + 1 := by field_simp
    have hbase : ((n : ℝ) + 1) ^ σ ≤
        D ^ σ * (1 + ((n : ℝ) + 1) / D) := by
      calc
        ((n : ℝ) + 1) ^ σ =
            (D * (((n : ℝ) + 1) / D)) ^ σ := by rw [heq]
        _ = D ^ σ * (((n : ℝ) + 1) / D) ^ σ :=
          Real.mul_rpow hDpos.le hn
        _ ≤ D ^ σ * (1 + ((n : ℝ) + 1) / D) :=
          mul_le_mul_of_nonneg_left
            (rpow_le_one_add_of_exponent_Icc _ _ hn hσ0 hσ1) hDpow
    have hrn : 0 ≤ r ^ n := pow_nonneg hr0 _
    calc
      (((n : ℝ) + 1) ^ σ) * r ^ n ≤
          (D ^ σ * (1 + ((n : ℝ) + 1) / D)) * r ^ n :=
        mul_le_mul_of_nonneg_right hbase hrn
      _ = D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n)) := by ring
  have hrnorm : ‖r‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hs0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hrnorm
  have hs1 : Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) :=
    summable_add_one_mul_geometric hr0 hr1
  have hsdom : Summable (fun n : ℕ =>
      D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n))) :=
    ((hs0.add (hs1.mul_left D⁻¹)).mul_left (D ^ σ))
  have hslow : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ σ) * r ^ n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg
      (Real.rpow_nonneg (by positivity) σ) (pow_nonneg hr0 _)) hrpow hsdom
  have hsum := Summable.tsum_le_tsum hrpow hslow hsdom
  have hgap : 0 ≤ 1 - r := sub_nonneg.mpr hr1.le
  have hgeom : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
    tsum_geometric_of_norm_lt_one hrnorm
  have hlin := tsum_add_one_mul_geometric hr0 hr1
  have hgap_ne : 1 - r ≠ 0 := ne_of_gt (sub_pos.mpr hr1)
  calc
    (1 - r) * (∑' n : ℕ, (((n : ℝ) + 1) ^ σ) * r ^ n) ≤
        (1 - r) * (∑' n : ℕ,
          D ^ σ * (r ^ n + D⁻¹ * (((n : ℝ) + 1) * r ^ n))) :=
      mul_le_mul_of_nonneg_left hsum hgap
    _ = D ^ σ * (1 + 1 / (D * (1 - r))) := by
      rw [tsum_mul_left, Summable.tsum_add hs0 (hs1.mul_left D⁻¹),
        tsum_mul_left, hgeom, hlin]
      field_simp
    _ ≤ 3 * D ^ σ := by
      nlinarith [mul_nonneg hDpow (sub_nonneg.mpr hscale)]
end OAI.ShortDraftHeckeBridge
