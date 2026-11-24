-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic.radius_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:17:27.720296+00:00
-- url     : https://prove2.me/submissions/e2941ed9-c437-4284-8ab8-8334fd3dd671

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussianSumOfCounting

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
namespace GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
theorem _root_.solution (n j : ℕ) {t₀ t : ℝ} (ht₀ : 0 < t₀) (ht : t₀ ≤ t) :
    (2 ^ j / Real.sqrt t) ^ n + (2 ^ j / Real.sqrt t) ^ (2 * n) ≤
      ((4 : ℝ) ^ n) ^ j * ((1 + (Real.sqrt t₀ ^ n)⁻¹) * (Real.sqrt t ^ n)⁻¹) := by
  have hs₀ : 0 < Real.sqrt t₀ := Real.sqrt_pos.mpr ht₀
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr (ht₀.trans_le ht)
  have hle : Real.sqrt t₀ ≤ Real.sqrt t := Real.sqrt_le_sqrt ht
  set A : ℝ := ((2 : ℝ) ^ j) ^ n with hA
  set B : ℝ := (Real.sqrt t ^ n)⁻¹ with hB
  set B₀ : ℝ := (Real.sqrt t₀ ^ n)⁻¹ with hB₀
  have hA1 : 1 ≤ A := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hBpos : 0 < B := by positivity
  have hBB : B ≤ B₀ := inv_anti₀ (by positivity) (pow_le_pow_left₀ hs₀.le hle n)
  have e1 : (2 ^ j / Real.sqrt t) ^ n = A * B := by
    rw [div_pow, hA, hB, div_eq_mul_inv]
  have e2 : (2 ^ j / Real.sqrt t) ^ (2 * n) = (A * B) ^ 2 := by
    rw [mul_comm 2 n, pow_mul, e1]
  have e3 : ((4 : ℝ) ^ n) ^ j = A ^ 2 := by
    rw [hA, ← pow_mul, ← pow_mul, ← pow_mul]
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, ← pow_mul]; congr 1; ring
  rw [e1, e2, e3]
  have h1 : A * B ≤ A ^ 2 * B := by
    apply mul_le_mul_of_nonneg_right _ hBpos.le
    nlinarith
  have h2 : (A * B) ^ 2 ≤ A ^ 2 * (B₀ * B) := by
    have : (A * B) ^ 2 = A ^ 2 * (B * B) := by ring
    rw [this]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_right hBB hBpos.le
  nlinarith
end GlobalTheory.CompanionTheory.SW.Core.GaussianDyadic
